// #![cfg_attr(all(not(test), not(feature = "std")), no_std)]

pub mod mock_flash;
pub mod tiny_mock_flash;

/// The log message has not been sent or cleared
pub const HEADER_ACTIVE: u8 = 0b1100_0000;
/// This message has been cleared; it should not be sent/shown again
pub const HEADER_INACTIVE: u8 = 0b1000_0000;

#[derive(Debug)]
pub struct NvmLog<F, T> {
    next_log_addr: u32,
    flash: F,
    _marker: core::marker::PhantomData<T>,
}

pub struct NvmLogPosition {
    next_log_addr: u32,
}

#[derive(Debug)]
pub enum NvmLogError<F> {
    Flash(F),
    Postcard(postcard::Error),
}

type NvmLogResult<T, F> = Result<T, NvmLogError<F>>;

impl<T> From<T> for NvmLogError<T> {
    fn from(v: T) -> Self {
        NvmLogError::Flash(v)
    }
}

impl<F: embedded_storage::nor_flash::NorFlash, T> NvmLog<F, T> {
    pub fn new(flash: F) -> Self {
        Self {
            next_log_addr: 0,
            flash,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn free(self) -> F {
        self.flash
    }

    pub fn current_postition(&self) -> NvmLogPosition {
        NvmLogPosition {
            next_log_addr: self.next_log_addr,
        }
    }

    /// Restore the state of the NvmLog (specifically, where should the next message go)
    /// from the information stored in flash. Assumes that either there are valid logs there,
    /// or the used pages have been cleared
    pub fn restore_from_flash(flash: F) -> NvmLogResult<Self, F::Error> {
        let mut this = Self {
            next_log_addr: 0,
            flash,
            _marker: core::marker::PhantomData,
        };

        let num_pages = this.flash.capacity() / F::ERASE_SIZE;

        for next_page_start in (1..=num_pages).map(|x| x * F::ERASE_SIZE) {
            let mut page_end = [0, 0];
            this.flash.read(next_page_start as u32 - 2, &mut page_end)?;

            // a full (sealed) page always ends in NULL NULL. Hence, if this page
            // ends in a 0xFF then either it is only partially written, or it's completely
            // blank (meaning it's full of 0xFF's)
            if page_end == [0xFF, 0xFF] {
                match this.last_uncleared(next_page_start as u32)? {
                    None => {
                        // The whole page is filled with 0xFF's
                        this.next_log_addr = (next_page_start - F::ERASE_SIZE) as u32;
                    }
                    Some(last) => {
                        // Part of the page is filled; start after the last message
                        this.next_log_addr = last + 1;
                    }
                }

                // we have found the left-most page that has space available for new logs
                // that's what we were looking for; break and return
                break;
            }
        }

        Ok(this)
    }
}

impl<F: embedded_storage::nor_flash::MultiwriteNorFlash, T> NvmLog<F, T> {
    pub fn erase_up_to_position(
        &mut self,
        position: &NvmLogPosition,
    ) -> NvmLogResult<(), F::Error> {
        // find the next message
        let next_boundary = match self.next_message_boundary(self.next_log_addr)? {
            None => {
                // loop back around
                match self.next_message_boundary(0)? {
                    None => todo!("no logs at all"),
                    Some(uncleared) => page_start(uncleared, F::ERASE_SIZE as u32),
                }
            }
            Some(uncleared) => page_start(uncleared, F::ERASE_SIZE as u32),
        };

        let it = MsgIndexIter {
            nvm_log: self,
            stop_at: position.next_log_addr,
            next_log_addr: next_boundary,
        };

        for _ in it {
            // do nothing
        }

        Ok(())
    }
}

impl<F, T> NvmLog<F, T>
where
    F: embedded_storage::nor_flash::NorFlash,
    T: serde::de::DeserializeOwned,
{
    pub fn iter(&mut self) -> NvmLogIter<'_, F, T> {
        NvmLogIter {
            result_iter: self.result_iter(),
        }
    }

    pub fn result_iter(&mut self) -> NvmLogResultIter<'_, F, T> {
        match self.result_iter_help() {
            Ok(iter) => iter,
            Err(e) => panic!("implementation error"),
        }
    }

    fn result_iter_help(&mut self) -> NvmLogResult<NvmLogResultIter<'_, F, T>, F::Error> {
        // find the next message
        let next_boundary = match self.next_message_boundary(self.next_log_addr)? {
            None => {
                // loop back around
                match self.next_message_boundary(0)? {
                    None => todo!("no logs at all"),
                    Some(uncleared) => page_start(uncleared, F::ERASE_SIZE as u32),
                }
            }
            Some(uncleared) => page_start(uncleared, F::ERASE_SIZE as u32),
        };

        let iter = NvmLogResultIter {
            next_log_addr: next_boundary,
            nvm_log: self,
        };

        Ok(iter)
    }
}

const WORKING_BUF_SIZE: usize = 1024;

#[derive(Debug)]
enum CrossPageBoundary {
    FitsInCurrentPage,
    NextPage { start_address: usize },
    BackToTheBeginning,
}

fn crosses_page_boundary<F>(flash: &F, start_address: usize, buf: &[u8]) -> CrossPageBoundary
where
    F: embedded_storage::nor_flash::NorFlash,
{
    let end_address = start_address + buf.len();

    assert!(end_address - start_address <= F::ERASE_SIZE);

    let ends_at_page_boundary = end_address % F::ERASE_SIZE == 0;
    let starts_at_page_boundary = start_address % F::ERASE_SIZE == 0;
    let crosses_page_boundary =
        (start_address / F::ERASE_SIZE) != ((end_address - 1) / F::ERASE_SIZE);

    if starts_at_page_boundary || crosses_page_boundary {
        if end_address > flash.capacity() {
            CrossPageBoundary::BackToTheBeginning
        } else {
            CrossPageBoundary::NextPage {
                start_address: page_start(end_address as u32, F::ERASE_SIZE as u32) as usize,
            }
        }
    } else if ends_at_page_boundary {
        if end_address == flash.capacity() {
            CrossPageBoundary::BackToTheBeginning
        } else {
            CrossPageBoundary::NextPage {
                start_address: page_start(end_address as u32 + 1, F::ERASE_SIZE as u32) as _,
            }
        }
    } else {
        println!("Fits in current page: {} .. {}", start_address, end_address);
        CrossPageBoundary::FitsInCurrentPage
    }
}

impl<F: embedded_storage::nor_flash::NorFlash, T: serde::Serialize> NvmLog<F, T> {
    pub fn store(&mut self, value: T) -> NvmLogResult<(), F::Error> {
        let mut buf = [0u8; WORKING_BUF_SIZE];
        buf[0] = HEADER_ACTIVE;
        let used = 1 + postcard::to_slice_cobs(&value, &mut buf[1..])
            .map_err(NvmLogError::Postcard)?
            .len();

        let bytes = &mut buf[..used];

        self.store_help(bytes)
    }

    fn write_zeros(&mut self, start: u32, end: u32) -> NvmLogResult<(), F::Error> {
        for index in start..end {
            self.flash.write(index, &[0])?;
        }

        Ok(())
    }

    fn store_help(&mut self, bytes: &mut [u8]) -> NvmLogResult<(), F::Error> {
        use CrossPageBoundary::*;
        match crosses_page_boundary(&self.flash, self.next_log_addr as usize, bytes) {
            FitsInCurrentPage => {
                // don't need to erase anything
                self.flash.write(self.next_log_addr, bytes)?;
                self.next_log_addr += bytes.len() as u32;
            }
            NextPage { start_address } => {
                // pad the current page with zeros
                let current = self.next_log_addr;

                if current != start_address as u32 {
                    assert!(start_address % F::ERASE_SIZE == 0);

                    self.write_zeros(current, start_address as u32)?;

                    self.next_log_addr += bytes.len() as u32;
                }

                // we will (partially) write into the next page; we must erase it first
                let start_address = start_address as u32;
                let end_address = start_address + F::ERASE_SIZE as u32;
                self.flash.erase(start_address, end_address)?;

                self.flash.write(self.next_log_addr, bytes)?;
                self.next_log_addr += bytes.len() as u32;
            }
            BackToTheBeginning => {
                // we pad the current page with zeros
                let current = self.next_log_addr;
                let next_page_start_address = self.flash.capacity();

                assert!(next_page_start_address % F::ERASE_SIZE == 0);

                self.write_zeros(current, next_page_start_address as u32)?;

                let start_address = 0u32;
                let end_address = start_address + F::ERASE_SIZE as u32;
                self.flash.erase(start_address, end_address)?;

                self.flash.write(0, bytes)?;

                self.next_log_addr = bytes.len() as u32;
            }
        }

        Ok(())
    }
}

impl<F: embedded_storage::nor_flash::ReadNorFlash, T> NvmLog<F, T> {
    fn next_message_boundary(&mut self, start: u32) -> NvmLogResult<Option<u32>, F::Error> {
        for offset in start as usize..self.flash.capacity() - 1 {
            let mut word = [0, 0];
            self.flash
                .read(offset as u32, &mut word)
                .unwrap_or_else(|_| panic!());

            // a NULL bytes is the Cobs message sentinal (end) value
            if word[0] == 0 && word[1] != 0 {
                return Ok(Some(offset as u32));
            }
        }

        {
            let offset = self.flash.capacity() as u32;
            let mut word = [0];
            self.flash
                .read(offset - 1, &mut word)
                .unwrap_or_else(|_| panic!());

            // a NULL bytes is the Cobs message sentinal (end) value
            if word[0] == 0 {
                return Ok(Some(offset));
            }
        }

        Ok(None)
    }

    fn first_uncleared(&mut self, start: u32) -> NvmLogResult<Option<u32>, F::Error> {
        for index in start..self.flash.capacity() as u32 {
            let mut output = [0];
            self.flash.read(index, &mut output)?;

            if output[0] != 0xFF {
                return Ok(Some(index));
            }
        }

        Ok(None)
    }

    fn last_uncleared(&mut self, end: u32) -> NvmLogResult<Option<u32>, F::Error> {
        for index in (0..end).rev() {
            let mut output = [0];
            self.flash.read(index, &mut output)?;

            if output[0] != 0xFF {
                return Ok(Some(index));
            }
        }

        Ok(None)
    }
}

pub struct NvmLogIter<'a, F, T> {
    result_iter: NvmLogResultIter<'a, F, T>,
}

impl<'a, F, T> Iterator for NvmLogIter<'a, F, T>
where
    F: embedded_storage::nor_flash::NorFlash,
    T: serde::de::DeserializeOwned,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.result_iter.next()?.ok()
    }
}

pub struct NvmLogResultIter<'a, F, T> {
    nvm_log: &'a mut NvmLog<F, T>,
    next_log_addr: u32,
}

impl<'a, F, T> Iterator for NvmLogResultIter<'a, F, T>
where
    F: embedded_storage::nor_flash::NorFlash,
    T: serde::de::DeserializeOwned,
{
    type Item = NvmLogResult<T, F::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        dbg!(self.next_log_addr, self.nvm_log.next_log_addr);
        if self.next_log_addr == self.nvm_log.next_log_addr {
            return None;
        }

        let remaining_bytes = self.nvm_log.flash.capacity() - self.next_log_addr as usize;
        let remaining_bytes = remaining_bytes.min(WORKING_BUF_SIZE);

        let mut buf = [0xFF; WORKING_BUF_SIZE];
        let buf = &mut buf[..remaining_bytes];

        match self.nvm_log.flash.read(self.next_log_addr, buf) {
            Err(e) => Some(Err(NvmLogError::Flash(e))),
            Ok(()) => {
                match buf.iter().position(|x| *x == 0) {
                    None => {
                        // there is no message here, we need to go look at the start
                        self.next_log_addr = 0;
                        self.next()
                    }
                    Some(message_end) => {
                        let after_msg_end = buf.get(message_end + 1).copied();
                        let msg_buf = &mut buf[..message_end];

                        if msg_buf.is_empty() {
                            return None;
                        }

                        if let Some(0) = after_msg_end {
                            // this is the final message in the block
                            // look at the next block next

                            let capacity = self.nvm_log.flash.capacity() as u32;
                            let new = page_end(
                                self.next_log_addr + message_end as u32,
                                F::ERASE_SIZE as u32,
                            ) % capacity;

                            self.next_log_addr = new;
                        } else {
                            // +1 for the NULL sentinel
                            self.next_log_addr += msg_buf.len() as u32 + 1;
                        }

                        match msg_buf.get(0).copied() {
                            Some(HEADER_ACTIVE) => {
                                match postcard::from_bytes_cobs(&mut msg_buf[1..]) {
                                    Ok(e) => Some(Ok(e)),
                                    Err(e) => Some(Err(NvmLogError::Postcard(e))),
                                }
                            }
                            Some(HEADER_INACTIVE) => {
                                // this message is inactive, we don't even need to decode it; on to
                                // the next one
                                self.next()
                            }
                            _ => unreachable!("this should never happen"),
                        }
                    }
                }
            }
        }
    }
}

pub struct MsgIndexIter<'a, F, T> {
    nvm_log: &'a mut NvmLog<F, T>,
    stop_at: u32,
    next_log_addr: u32,
}

impl<'a, F, T> Iterator for MsgIndexIter<'a, F, T>
where
    F: embedded_storage::nor_flash::NorFlash,
{
    type Item = NvmLogResult<u32, F::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        dbg!(self.next_log_addr, self.stop_at);
        if self.next_log_addr == self.nvm_log.next_log_addr || self.next_log_addr == self.stop_at {
            return None;
        }

        let remaining_bytes = self.nvm_log.flash.capacity() - self.next_log_addr as usize;
        let remaining_bytes = remaining_bytes.min(WORKING_BUF_SIZE);

        let mut buf = [0xFF; WORKING_BUF_SIZE];
        let buf = &mut buf[..remaining_bytes];

        let current_index = self.next_log_addr;
        match self.nvm_log.flash.read(self.next_log_addr, buf) {
            Err(e) => Some(Err(NvmLogError::Flash(e))),
            Ok(()) => {
                match buf.iter().position(|x| *x == 0) {
                    None => {
                        // there is no message here, we need to go look at the start
                        self.next_log_addr = 0;
                        self.next()
                    }
                    Some(message_end) => {
                        let after_msg_end = buf.get(message_end + 1).copied();
                        let msg_buf = &mut buf[..message_end];

                        if msg_buf.is_empty() {
                            return None;
                        }

                        if let Some(0) = after_msg_end {
                            // this is the final message in the block
                            // look at the next block next

                            let capacity = self.nvm_log.flash.capacity();
                            let current_page =
                                (self.next_log_addr as usize + message_end) / F::ERASE_SIZE;
                            let new = (((current_page + 1) * F::ERASE_SIZE) % capacity) as u32;

                            let range = self.next_log_addr..new;

                            if range.contains(&self.stop_at) {
                                self.stop_at = new;
                            }

                            self.next_log_addr = new;
                        } else {
                            // +1 for the NULL sentinel
                            self.next_log_addr += msg_buf.len() as u32 + 1;
                        }

                        eprintln!("erasing at index {}", current_index);
                        match msg_buf.get(0).copied() {
                            Some(HEADER_ACTIVE) => {
                                let header_addr = current_index;
                                match self.nvm_log.flash.write(header_addr, &[HEADER_INACTIVE]) {
                                    Err(e) => Some(Err(NvmLogError::Flash(e))),
                                    Ok(()) => Some(Ok(0)),
                                }
                            }
                            Some(HEADER_INACTIVE) => {
                                // already inactive, do nothing
                                Some(Ok(0))
                            }
                            _ => unreachable!("this should never happen"),
                        }
                    }
                }
            }
        }
    }
}

fn page_start(address: u32, page_size: u32) -> u32 {
    (address / page_size) * page_size
}

fn page_end(address: u32, page_size: u32) -> u32 {
    page_start(address, page_size) + page_size
}
