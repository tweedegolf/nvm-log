#![cfg_attr(all(not(test), not(feature = "std")), no_std)]

use core::ops::ControlFlow;

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

#[derive(Debug, Default, Clone, Copy)]
pub struct NvmLogPosition {
    next_log_addr: u32,
}

fn last_uncleared<F>(flash: &mut F, end: u32) -> NvmLogResult<Option<u32>, F::Error>
where
    F: embedded_storage::nor_flash::NorFlash,
{
    let mut bytes = [0; 16];
    let bytes = &mut bytes[..F::WRITE_SIZE];

    for index in (0..end).step_by(F::WRITE_SIZE).rev() {
        flash.read(index, bytes)?;

        if bytes.iter().any(|x| *x != 0xFF) {
            return Ok(Some(index));
        }
    }

    Ok(None)
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

    pub fn new_infer_position(mut flash: F) -> Self {
        let position = Self::restore_from_flash(&mut flash).unwrap();

        Self::new_at_position(flash, position)
    }

    pub fn new_at_position(flash: F, position: NvmLogPosition) -> Self {
        Self {
            next_log_addr: position.next_log_addr,
            flash,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn free(self) -> (F, NvmLogPosition) {
        let position = self.current_position();
        (self.flash, position)
    }

    pub fn current_position(&self) -> NvmLogPosition {
        NvmLogPosition {
            next_log_addr: self.next_log_addr,
        }
    }

    /// Restore the state of the NvmLog (specifically, where should the next message go)
    /// from the information stored in flash. Assumes that either there are valid logs there,
    /// or the used pages have been cleared
    pub fn restore_from_flash(flash: &mut F) -> NvmLogResult<NvmLogPosition, F::Error> {
        let num_pages = flash.capacity() / F::ERASE_SIZE;

        let mut position = NvmLogPosition::default();

        for next_page_start in (1..=num_pages).map(|x| x * F::ERASE_SIZE) {
            let page_end = &mut [0; 16];
            let page_end = &mut page_end[..F::WRITE_SIZE];
            flash.read(next_page_start as u32 - F::WRITE_SIZE as u32, page_end)?;

            // a full (sealed) page always ends in NULL. Hence, if this page
            // ends in a 0xFF then either it is only partially written, or it's completely
            // blank (meaning it's full of 0xFF's)
            if page_end.ends_with(&[0xFF]) {
                match last_uncleared(flash, next_page_start as u32)? {
                    None => {
                        // The whole page is filled with 0xFF's
                        position.next_log_addr = (next_page_start - F::ERASE_SIZE) as u32;
                    }
                    Some(last) => {
                        // Part of the page is filled; start after the last message
                        position.next_log_addr = round_to_multiple_of(last + 1, F::WRITE_SIZE as _);
                    }
                }

                // we have found the left-most page that has space available for new logs
                // that's what we were looking for; break and return
                break;
            }
        }

        Ok(position)
    }
}

impl<F: embedded_storage::nor_flash::MultiwriteNorFlash, T> NvmLog<F, T> {
    pub fn erase_up_to_position(
        &mut self,
        position: &NvmLogPosition,
    ) -> NvmLogResult<(), F::Error> {
        // find the next message
        let mut next_boundary = match self.next_message_start(self.next_log_addr)? {
            None => {
                // loop back around
                match self.next_message_start(0)? {
                    None => todo!("no logs at all"),
                    Some(uncleared) => page_start(uncleared, F::ERASE_SIZE as u32),
                }
            }
            Some(uncleared) => page_start(uncleared, F::ERASE_SIZE as u32),
        };

        let stop_at = position.next_log_addr;

        loop {
            match erase_step(self, next_boundary) {
                ControlFlow::Continue(new_next_boundary) => {
                    if new_next_boundary == stop_at {
                        return Ok(());
                    } else {
                        next_boundary = new_next_boundary;
                    }
                }
                ControlFlow::Break(done) => return done,
            }
        }
    }
}

fn round_to_multiple_of(value: u32, base: u32) -> u32 {
    (value + (base - 1)) / base * base
}

impl<F, T> NvmLog<F, T>
where
    F: embedded_storage::nor_flash::NorFlash,
    T: serde::de::DeserializeOwned,
{
    pub fn iter(self) -> NvmLogIter<F, T> {
        NvmLogIter {
            result_iter: self.result_iter(),
        }
    }

    pub fn result_iter(self) -> NvmLogResultIter<F, T> {
        match self.result_iter_help() {
            Ok(iter) => iter,
            Err(_e) => panic!("implementation error"),
        }
    }

    fn result_iter_help(mut self) -> NvmLogResult<NvmLogResultIter<F, T>, F::Error> {
        // find the next message
        let addr = self.next_log_addr;
        let next_boundary = match self.next_message_start(addr)? {
            None => 0,
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
    let crosses_page_boundary =
        (start_address / F::ERASE_SIZE) != ((end_address - 1) / F::ERASE_SIZE);

    if crosses_page_boundary {
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
        CrossPageBoundary::FitsInCurrentPage
    }
}

impl<F: embedded_storage::nor_flash::NorFlash, T: serde::Serialize> NvmLog<F, T> {
    pub fn store(&mut self, value: T) -> NvmLogResult<(), F::Error> {
        let mut buf = [0u8; WORKING_BUF_SIZE];
        buf[0] = HEADER_ACTIVE;
        let used_so_far = 1 + postcard::to_slice_cobs(&value, &mut buf[1..])
            .map_err(NvmLogError::Postcard)?
            .len();

        // pad to a multiple of the minimal write
        let used = round_to_multiple_of(used_so_far as _, F::WRITE_SIZE as _) as usize;

        for b in buf[used_so_far..used].iter_mut() {
            *b = 0;
        }

        let bytes = &mut buf[..used];

        self.store_help(bytes)
    }

    fn write_zeros(&mut self, mut start: u32, end: u32) -> NvmLogResult<(), F::Error> {
        const ZS: usize = 64;
        const ZEROS: [u8; ZS] = [0; ZS];

        while start != end {
            let remaining = (end - start).min(ZS as u32) as usize;

            self.flash.write(start, &ZEROS[..remaining])?;

            start += remaining as u32;
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
                self.write_zeros(self.next_log_addr, start_address as _)?;
                // we will (partially) write into the next page; we must erase it first
                let start_address = start_address as u32;
                let end_address = start_address + F::ERASE_SIZE as u32;
                self.flash.erase(start_address, end_address)?;

                self.flash.write(start_address, bytes)?;
                self.next_log_addr = start_address as u32 + bytes.len() as u32;
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

impl<F: embedded_storage::nor_flash::NorFlash, T> NvmLog<F, T> {
    fn next_message_start(&mut self, start: u32) -> NvmLogResult<Option<u32>, F::Error> {
        // TODO check first byte of the page to see if page has any messages
        let it = (start as usize..self.flash.capacity()).step_by(F::WRITE_SIZE);

        for offset in it {
            let word = &mut [0; 16];
            let word = &mut word[..F::WRITE_SIZE];
            self.flash.read(offset as u32, word)?;

            // a NULL bytes is the Cobs message sentinal (end) value
            // also we padd words with 0 bytes, so if the final byte
            // of the word is a NULL, the word must contain a NULL sentinel (and possibly some
            // padding), and the next word starts a new message (or is empty)
            if word[F::WRITE_SIZE - 1] == 0 {
                return Ok(Some((offset + F::WRITE_SIZE) as u32));
            }
        }

        Ok(None)
    }
}

pub struct NvmLogIter<F, T> {
    result_iter: NvmLogResultIter<F, T>,
}

impl<'a, F, T> Iterator for NvmLogIter<F, T>
where
    F: embedded_storage::nor_flash::NorFlash,
    T: serde::de::DeserializeOwned,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.result_iter.next()?.ok()
    }
}

#[derive(Debug)]
pub struct NvmLogResultIter<F, T> {
    nvm_log: NvmLog<F, T>,
    next_log_addr: u32,
}

impl<'a, F, T> NvmLogResultIter<F, T> {
    pub fn current_position(&self) -> NvmLogPosition {
        NvmLogPosition {
            next_log_addr: self.next_log_addr,
        }
    }

    pub fn free(self) -> NvmLog<F, T> {
        self.nvm_log
    }
}

impl<'a, F, T> Iterator for NvmLogResultIter<F, T>
where
    F: embedded_storage::nor_flash::NorFlash,
    T: serde::de::DeserializeOwned,
{
    type Item = NvmLogResult<T, F::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut scratchpad = [0xFF; WORKING_BUF_SIZE];
        let scratchpad_len = scratchpad.len();

        let current_index = self.next_log_addr;
        let remaining_bytes = self.nvm_log.flash.capacity() - current_index as usize;

        let current_bytes = &mut scratchpad[..remaining_bytes.min(scratchpad_len)];
        match self.nvm_log.flash.read(current_index, current_bytes) {
            Err(_) => todo!(),
            Ok(()) => {
                match current_bytes.get(0).copied() {
                    None => {
                        if current_index != 0 {
                            self.next_log_addr = 0;
                            self.next()
                        } else {
                            // no bytes could be read; iterator is empty
                            None
                        }
                    }
                    Some(0) => {
                        // skip ahead to the next message
                        let next_message_start = self
                            .nvm_log
                            .next_message_start(current_index)
                            .unwrap() // TODO remove unwrap?
                            .unwrap_or(0);

                        self.next_log_addr = next_message_start;

                        self.next()
                    }
                    Some(0xFF) => {
                        // hit unused memory; we're done here
                        None
                    }
                    Some(HEADER_ACTIVE) => {
                        let next_message_start = self
                            .nvm_log
                            .next_message_start(current_index)
                            .unwrap() // TODO remove unwrap?
                            .unwrap_or(0);

                        self.next_log_addr = next_message_start;

                        let max_message_length = next_message_start - current_index;

                        let message_bytes = &mut current_bytes[1..max_message_length as usize];

                        match postcard::from_bytes_cobs(message_bytes) {
                            Ok(e) => Some(Ok(e)),
                            Err(e) => Some(Err(NvmLogError::Postcard(e))),
                        }
                    }
                    Some(HEADER_INACTIVE) => {
                        let next_message_start = self
                            .nvm_log
                            .next_message_start(current_index)
                            .unwrap() // TODO remove unwrap?
                            .unwrap_or(0);

                        self.next_log_addr = next_message_start;

                        self.next()
                    }
                    Some(other) => unreachable!(
                        r"a word in this position MUST be one of the above options, got {} (hex: {:x?})",
                        other, other
                    ),
                }
            }
        }
    }
}

/// Set the header to inactive,
/// leave other bytes of the word unchanged (assuming NOR flash)
const INACTIVES: [u8; 16] = {
    let mut value = [0xFF; 16];
    value[0] = HEADER_INACTIVE;
    value
};

fn erase_step<F, T>(
    nvm_log: &mut NvmLog<F, T>,
    next_log_addr: u32,
) -> ControlFlow<NvmLogResult<(), F::Error>, u32>
where
    F: embedded_storage::nor_flash::MultiwriteNorFlash,
{
    let mut scratchpad = [0xFF; WORKING_BUF_SIZE];
    let scratchpad_len = scratchpad.len();

    let current_index = next_log_addr;
    let remaining_bytes = nvm_log.flash.capacity() - current_index as usize;

    let current_bytes = &mut scratchpad[..remaining_bytes.min(scratchpad_len)];

    macro_rules! next_message_start {
        () => {{
            match nvm_log.next_message_start(current_index) {
                Err(e) => {
                    // propagate errors
                    return ControlFlow::Break(Err(e));
                }
                Ok(value) => {
                    // if None, wrap around to the beginning
                    value.unwrap_or(0)
                }
            }
        }};
    }

    match nvm_log.flash.read(current_index, current_bytes) {
        Err(e) => ControlFlow::Break(Err(NvmLogError::Flash(e))),
        Ok(()) => {
            match current_bytes.get(0).copied() {
                None => {
                    // no bytes could be read; iterator is empty
                    ControlFlow::Break(Ok(()))
                }
                Some(0) => {
                    // skip ahead to the next message
                    ControlFlow::Continue(next_message_start!())
                }
                Some(0xFF) => {
                    // hit unused memory; we're done here
                    ControlFlow::Break(Ok(()))
                }
                Some(HEADER_ACTIVE) => {
                    // flip the header
                    let flash = &mut nvm_log.flash;
                    match flash.write(current_index, &INACTIVES[..F::WRITE_SIZE]) {
                        Err(e) => ControlFlow::Break(Err(NvmLogError::Flash(e))),
                        Ok(()) => ControlFlow::Continue(next_message_start!()),
                    }
                }
                Some(HEADER_INACTIVE) => {
                    // skip to next message
                    ControlFlow::Continue(next_message_start!())
                }
                Some(other) => unreachable!(
                    "a word in this position MUST be one of the above options, got {} (hex: {:x?})",
                    other, other
                ),
            }
        }
    }
}

fn page_start(address: u32, page_size: u32) -> u32 {
    (address / page_size) * page_size
}
