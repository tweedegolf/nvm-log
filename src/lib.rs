#![cfg_attr(all(not(test), not(feature = "std")), no_std)]

use core::ops::{ControlFlow, Range};

pub mod mock_flash;
pub mod tiny_mock_flash;

/// The log message has not been sent or cleared
pub const HEADER_ACTIVE: u8 = 0b1100_0000;
/// This message has been cleared; it should not be sent/shown again
pub const HEADER_INACTIVE: u8 = 0b1000_0000;

/// Must be bigger than any individual message
const WORKING_BUF_SIZE: usize = 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct NvmLogPosition {
    /// index of the first byte of the next message
    next_log_addr: u32,
}

#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum NvmLogError<F> {
    Flash(F),
    Postcard(postcard::Error),
    /// Some of the data in the flash is invalid and we probably can't recover from it.
    /// The application should consider erasing the nvm_log flash.
    InvalidFlashState,
}

type NvmLogResult<T, F> = Result<T, NvmLogError<F>>;

impl<T: embedded_storage::nor_flash::NorFlashError> From<T> for NvmLogError<T> {
    fn from(v: T) -> Self {
        NvmLogError::Flash(v)
    }
}

#[derive(Debug)]
pub struct NvmLog<F, T> {
    next_log_addr: u32,
    assigned_region: Range<u32>,
    flash: F,
    _marker: core::marker::PhantomData<T>,
}

impl<F: Clone, T> Clone for NvmLog<F, T> {
    fn clone(&self) -> Self {
        Self {
            next_log_addr: self.next_log_addr,
            flash: self.flash.clone(),
            _marker: self._marker,
            assigned_region: self.assigned_region.clone(),
        }
    }
}

impl<F: embedded_storage::nor_flash::NorFlash, T> NvmLog<F, T> {
    pub fn new(flash: F, assigned_region: Range<u32>) -> Self {
        Self::new_at_position(
            flash,
            NvmLogPosition {
                next_log_addr: assigned_region.start,
            },
            assigned_region,
        )
    }

    pub fn new_infer_position(
        mut flash: F,
        assigned_region: Range<u32>,
    ) -> NvmLogResult<Self, F::Error> {
        let position = Self::infer_position_from_flash(&mut flash, assigned_region.clone())?;

        Ok(Self::new_at_position(flash, position, assigned_region))
    }

    pub fn new_at_position(
        flash: F,
        position: NvmLogPosition,
        assigned_region: Range<u32>,
    ) -> Self {
        assert!(assigned_region.contains(&position.next_log_addr));

        Self {
            next_log_addr: position.next_log_addr,
            flash,
            _marker: core::marker::PhantomData,
            assigned_region,
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

    /// erase all pages, reset position
    pub fn erase_all(&mut self) -> NvmLogResult<(), F::Error> {
        self.flash
            .erase(self.assigned_region.start, self.assigned_region.end)?;

        self.next_log_addr = self.assigned_region.start;

        Ok(())
    }

    /// Restore the state of the NvmLog (specifically, where should the next message go)
    /// from the information stored in flash. Assumes that either there are valid logs there,
    /// or the used pages have been cleared
    pub fn infer_position_from_flash(
        flash: &mut F,
        assigned_region: Range<u32>,
    ) -> NvmLogResult<NvmLogPosition, F::Error> {
        #[cfg(feature = "defmt")]
        defmt::debug!("Inferring position from flash...");
        let start_page = (assigned_region.start as usize) / F::ERASE_SIZE;
        let num_pages = assigned_region.len() / F::ERASE_SIZE;

        for page_index in start_page..start_page + num_pages {
            #[cfg(feature = "defmt")]
            defmt::trace!("Page: {}", page_index);
            let page_start = (page_index * F::ERASE_SIZE) as u32;

            if page_is_completely_blank(flash, page_start)? {
                #[cfg(feature = "defmt")]
                defmt::trace!("Page is completely blank");
                // skip this page
            } else if page_is_partially_blank(flash, page_start)? {
                #[cfg(feature = "defmt")]
                defmt::trace!("Page is partially blank");
                match page_first_clear_index(flash, page_start)? {
                    None => {
                        unreachable!("The page is partially blank, but we found only 0xFF bytes");
                    }
                    Some(last) => {
                        // we have found the left-most page that has space available for new logs
                        // that's what we were looking for; break and return
                        let next_log_addr = round_to_multiple_of(last + 1, F::WRITE_SIZE as _);
                        #[cfg(feature = "defmt")]
                        defmt::trace!(
                            "First clear index: {:#X}. Next log addr {:#X}",
                            last,
                            next_log_addr
                        );
                        return Ok(NvmLogPosition { next_log_addr });
                    }
                }
            }
            #[cfg(feature = "defmt")]
            defmt::trace!("Page is full");
        }
        #[cfg(feature = "defmt")]
        defmt::trace!("All pages are blank");
        // all pages are blank; start at the front
        Ok(NvmLogPosition {
            next_log_addr: assigned_region.start,
        })
    }
}

impl<F: embedded_storage::nor_flash::MultiwriteNorFlash, T> NvmLog<F, T> {
    pub fn deactivate_up_to_position(
        &mut self,
        position: &NvmLogPosition,
    ) -> NvmLogResult<(), F::Error> {
        // find the next message
        let mut next_boundary = match self.next_message_start(self.next_log_addr)? {
            None => {
                // loop back around
                match self.next_message_start(self.assigned_region.start)? {
                    None => {
                        // there are no logs at all; we're done
                        return Ok(());
                    }
                    Some(uncleared) => page_start(uncleared, F::ERASE_SIZE as u32),
                }
            }
            Some(uncleared) => page_start(uncleared, F::ERASE_SIZE as u32),
        };

        let stop_at = position.next_log_addr;

        loop {
            match deactivate_message_step(self, next_boundary) {
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

impl<F, T> NvmLog<F, T>
where
    F: embedded_storage::nor_flash::NorFlash,
    T: serde::de::DeserializeOwned,
{
    pub fn result_iter(&mut self) -> NvmLogResult<NvmLogResultIter<F, T>, F::Error> {
        // find the next message
        #[cfg(feature = "defmt")]
        defmt::debug!("NvmLog::result_iter");
        let addr = self.next_log_addr;
        let next_boundary = match self.next_message_start(addr)? {
            None => self.assigned_region.start,
            Some(uncleared) => page_start(uncleared, F::ERASE_SIZE as u32),
        };
        #[cfg(feature = "defmt")]
        defmt::trace!("Next boundary: {:#X}", next_boundary);

        let iter = NvmLogResultIter {
            next_log_addr: next_boundary,
            nvm_log: self,
        };

        Ok(iter)
    }
}

#[derive(Debug)]
enum CrossPageBoundary {
    FitsInCurrentPage,
    NextPage { start_address: usize },
    BackToTheBeginning,
}

fn crosses_page_boundary<F>(
    start_address: usize,
    buf: &[u8],
    assigned_region: Range<u32>,
) -> CrossPageBoundary
where
    F: embedded_storage::nor_flash::NorFlash,
{
    let end_address = start_address + buf.len();

    assert!(end_address - start_address <= F::ERASE_SIZE);

    let ends_at_page_boundary = end_address % F::ERASE_SIZE == 0;
    let crosses_page_boundary =
        (start_address / F::ERASE_SIZE) != ((end_address - 1) / F::ERASE_SIZE);

    if crosses_page_boundary {
        if end_address > assigned_region.end as usize {
            CrossPageBoundary::BackToTheBeginning
        } else {
            CrossPageBoundary::NextPage {
                start_address: page_start(end_address as u32, F::ERASE_SIZE as u32) as usize,
            }
        }
    } else if ends_at_page_boundary {
        if end_address == assigned_region.end as usize {
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

        self.store_help(&mut buf[..used])
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
        match crosses_page_boundary::<F>(
            self.next_log_addr as usize,
            bytes,
            self.assigned_region.clone(),
        ) {
            FitsInCurrentPage => {
                // don't need to erase anything
                self.flash.write(self.next_log_addr, bytes)?;
                self.next_log_addr += bytes.len() as u32;
            }
            NextPage { start_address } => {
                // The message is too big to fit into the current page.
                // 1. We first seal the current page with zeros
                self.write_zeros(self.next_log_addr, start_address as _)?;

                // 2. we will write into the next page; we must erase it first
                let start_address = start_address as u32;
                let end_address = start_address + F::ERASE_SIZE as u32;
                self.flash.erase(start_address, end_address)?;

                // 3. write the message at the start of the next page
                self.flash.write(start_address, bytes)?;
                self.next_log_addr = start_address as u32 + bytes.len() as u32;
            }
            BackToTheBeginning => {
                // The message does not fit in the current (which is the last) page
                let current = self.next_log_addr;
                let next_page_start_address = self.assigned_region.end as usize;

                assert!(next_page_start_address % F::ERASE_SIZE == 0);

                // 1. We first seal the current page with zeros
                self.write_zeros(current, next_page_start_address as u32)?;

                // 2. we will write into the first page; we must erase it first
                let start_address = self.assigned_region.start;
                let end_address = start_address + F::ERASE_SIZE as u32;
                self.flash.erase(start_address, end_address)?;

                // 3. write the message at the start of the first page
                self.flash.write(self.assigned_region.start, bytes)?;
                self.next_log_addr = self.assigned_region.start + bytes.len() as u32;
            }
        }

        Ok(())
    }
}

impl<F: embedded_storage::nor_flash::NorFlash, T> NvmLog<F, T> {
    pub(crate) fn next_message_start(&mut self, start: u32) -> NvmLogResult<Option<u32>, F::Error> {
        #[cfg(feature = "defmt")]
        defmt::debug!("getting next message from start ({:#X})...", start);
        let mut it = (self.assigned_region.start..self.assigned_region.end)
            .cycle()
            .skip(start as usize)
            .take(self.assigned_region.len())
            .step_by(F::WRITE_SIZE);

        while let Some(offset) = it.next() {
            let offset = offset as u32;
            #[cfg(feature = "defmt")]
            defmt::trace!("Offset: {:#X}", offset);

            // check if the page is completely empty; if so, skip it completely
            let is_page_start = page_start(offset, F::ERASE_SIZE as u32) == offset;
            #[cfg(feature = "defmt")]
            defmt::trace!("Is page start: {}", is_page_start);
            if is_page_start && page_is_completely_blank(&mut self.flash, offset)? {
                #[cfg(feature = "defmt")]
                defmt::debug!("Page is completely blank. Advance to next page");
                // advance to the next page
                for _ in 0..(F::ERASE_SIZE / F::WRITE_SIZE - 1) {
                    it.next();
                }

                continue;
            }

            let word = &mut [0; 16];
            let word = &mut word[..F::WRITE_SIZE];
            self.flash.read(offset, word)?;

            // a NULL bytes is the Cobs message sentinal (end) value
            // also we padd words with 0 bytes, so if the final byte
            // of the word is a NULL, the word must contain a NULL sentinel (and possibly some
            // padding), and the next word starts a new message (or is empty)
            if word.ends_with(&[0]) {
                let next_offset = self.assigned_region.start
                    + (offset + F::WRITE_SIZE as u32) % self.assigned_region.len() as u32;

                #[cfg(feature = "defmt")]
                defmt::debug!("Next message at {:#X}", next_offset);
                return Ok(Some(next_offset));
            }
        }
        #[cfg(feature = "defmt")]
        defmt::debug!("None");
        Ok(None)
    }
}

#[derive(Debug)]
pub struct NvmLogResultIter<'a, F, T> {
    nvm_log: &'a mut NvmLog<F, T>,
    next_log_addr: u32,
}

impl<'a, F, T> NvmLogResultIter<'a, F, T> {
    pub fn current_position(&self) -> NvmLogPosition {
        NvmLogPosition {
            next_log_addr: self.next_log_addr,
        }
    }
}

impl<'a, F, T> Iterator for NvmLogResultIter<'a, F, T>
where
    F: embedded_storage::nor_flash::NorFlash,
    T: serde::de::DeserializeOwned,
{
    type Item = NvmLogResult<T, F::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        'outer: loop {
            let current_index = self.next_log_addr;
            let remaining_bytes =
                self.nvm_log.assigned_region.end as usize - current_index as usize;
            #[cfg(feature = "defmt")]
            defmt::trace!(
                "Iter next at index 0x{:X} and remaining bytes: 0x{:X}",
                current_index,
                remaining_bytes
            );

            let first_byte = &mut [0][..remaining_bytes.min(1)];
            let answer = match self.nvm_log.flash.read(current_index, first_byte) {
                Err(e) => Some(Err(NvmLogError::Flash(e))),
                Ok(()) => {
                    match first_byte.get(0).copied() {
                        None => {
                            if current_index != 0 {
                                self.next_log_addr = self.nvm_log.assigned_region.start;
                                continue 'outer;
                            } else {
                                // no bytes could be read; iterator is empty
                                None
                            }
                        }
                        Some(0) => {
                            // skip ahead to the next message
                            let next_message_start =
                                match self.nvm_log.next_message_start(current_index) {
                                    Ok(Some(start)) => start,
                                    Ok(None) => self.nvm_log.assigned_region.start,
                                    Err(e) => return Some(Err(e)),
                                };

                            self.next_log_addr = next_message_start;

                            continue 'outer;
                        }
                        Some(0xFF) => {
                            // hit unused memory; we're done here
                            None
                        }
                        Some(HEADER_ACTIVE) => {
                            let mut scratchpad = [0xFF; WORKING_BUF_SIZE];
                            let scratchpad_len = scratchpad.len();

                            let current_index = self.next_log_addr;
                            let remaining_bytes =
                                self.nvm_log.assigned_region.end as usize - current_index as usize;

                            let current_bytes =
                                &mut scratchpad[..remaining_bytes.min(scratchpad_len)];

                            if let Err(e) = self.nvm_log.flash.read(current_index, current_bytes) {
                                return Some(Err(NvmLogError::Flash(e)));
                            }

                            let next_message_start =
                                match self.nvm_log.next_message_start(current_index) {
                                    Ok(Some(start)) => start,
                                    Ok(None) => self.nvm_log.assigned_region.start,
                                    Err(e) => return Some(Err(e)),
                                };

                            self.next_log_addr = next_message_start;

                            let max_message_length = next_message_start - current_index;

                            let message_bytes = &mut current_bytes[1..max_message_length as usize];

                            match postcard::from_bytes_cobs(message_bytes) {
                                Ok(e) => Some(Ok(e)),
                                Err(e) => Some(Err(NvmLogError::Postcard(e))),
                            }
                        }
                        Some(HEADER_INACTIVE) => {
                            let next_message_start =
                                match self.nvm_log.next_message_start(current_index) {
                                    Ok(Some(start)) => start,
                                    Ok(None) => self.nvm_log.assigned_region.start,
                                    Err(e) => return Some(Err(e)),
                                };

                            self.next_log_addr = next_message_start;

                            continue 'outer;
                        }
                        Some(_) => Some(Err(NvmLogError::InvalidFlashState)),
                    }
                }
            };

            return answer;
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

fn deactivate_message_step<F, T>(
    nvm_log: &mut NvmLog<F, T>,
    next_log_addr: u32,
) -> ControlFlow<NvmLogResult<(), F::Error>, u32>
where
    F: embedded_storage::nor_flash::MultiwriteNorFlash,
{
    let current_index = next_log_addr;
    let remaining_bytes = nvm_log.assigned_region.end as usize - current_index as usize;

    let first_byte = &mut [0][..remaining_bytes.min(1)];

    macro_rules! next_message_start {
        () => {{
            match nvm_log.next_message_start(current_index) {
                Err(e) => {
                    // propagate errors
                    return ControlFlow::Break(Err(e));
                }
                Ok(value) => {
                    // if None, wrap around to the beginning
                    value.unwrap_or(nvm_log.assigned_region.start)
                }
            }
        }};
    }

    match nvm_log.flash.read(current_index, first_byte) {
        Err(e) => ControlFlow::Break(Err(NvmLogError::Flash(e))),
        Ok(()) => {
            match first_byte.get(0).copied() {
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
                Some(_) => ControlFlow::Break(Err(NvmLogError::InvalidFlashState)),
            }
        }
    }
}

fn round_to_multiple_of(value: u32, base: u32) -> u32 {
    (value + (base - 1)) / base * base
}

fn page_start(address: u32, page_size: u32) -> u32 {
    (address / page_size) * page_size
}

fn page_is_partially_blank<F>(flash: &mut F, page_start: u32) -> NvmLogResult<bool, F::Error>
where
    F: embedded_storage::nor_flash::NorFlash,
{
    assert_eq!(page_start % F::ERASE_SIZE as u32, 0);

    let next_page_start = page_start + F::ERASE_SIZE as u32;

    let page_end = &mut [0; 16];
    let page_end = &mut page_end[..F::WRITE_SIZE];
    flash.read(next_page_start - F::WRITE_SIZE as u32, page_end)?;

    // a full (sealed) page always ends in NULL. Hence, if this page
    // ends in a 0xFF then either it is only partially written, or it's completely
    // blank (meaning it's full of 0xFF's)
    Ok(page_end.ends_with(&[0xFF]))
}

fn page_is_completely_blank<F>(flash: &mut F, page_start: u32) -> NvmLogResult<bool, F::Error>
where
    F: embedded_storage::nor_flash::NorFlash,
{
    assert_eq!(page_start % F::ERASE_SIZE as u32, 0);

    let page_start_word = &mut [0; 16];
    let page_start_word = &mut page_start_word[..F::WRITE_SIZE];
    flash.read(page_start, page_start_word)?;

    // messages cannot cross page boundaries. That means that the first byte of a used page must be
    // one of the HEADER constants. The only alternative is that the first byte is 0xFF indicating
    // blank memory
    Ok(page_start_word.starts_with(&[0xFF]))
}

fn page_first_clear_index<F>(flash: &mut F, page_start: u32) -> NvmLogResult<Option<u32>, F::Error>
where
    F: embedded_storage::nor_flash::NorFlash,
{
    assert_eq!(page_start % F::ERASE_SIZE as u32, 0);
    let next_page_start = page_start + F::ERASE_SIZE as u32;

    let mut bytes = [0; 16];
    let bytes = &mut bytes[..F::WRITE_SIZE];

    // start from the end, because 0xFFFFFFFF could be part of a message
    for index in (page_start..next_page_start).step_by(F::WRITE_SIZE).rev() {
        flash.read(index, bytes)?;

        if bytes.iter().any(|x| *x != 0xFF) {
            return Ok(Some(index));
        }
    }

    Ok(None)
}
