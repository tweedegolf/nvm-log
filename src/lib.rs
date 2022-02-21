// #![cfg_attr(all(not(test), not(feature = "std")), no_std)]

use std::ops::{Range, RangeBounds};

pub mod mock_flash;
pub mod tiny_mock_flash;

/// The log message has not been sent or cleared
pub const HEADER_ACTIVE: u8 = 0b1100_0000;
/// This message has been cleared; it should not be sent/shown again
pub const HEADER_INACTIVE: u8 = 0b1000_0000;

#[derive(Debug)]
pub struct NvmLog<F, T> {
    oldest_log_addr: u32,
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
            oldest_log_addr: 0,
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

    pub fn erase_up_to_position(&mut self, position: &NvmLogPosition) {
        self.oldest_log_addr = position.next_log_addr;
    }

    pub fn restore_from_flash(flash: F) -> NvmLogResult<Self, F::Error> {
        let mut this = Self {
            oldest_log_addr: 0,
            next_log_addr: 0,
            flash,
            _marker: core::marker::PhantomData,
        };

        let num_pages = this.flash.capacity() / F::ERASE_SIZE;

        for page in 1..=num_pages {
            let page_end = (page * F::ERASE_SIZE) as u32;
            let last_uncleared_byte = this.last_uncleared(page_end)?;

            match last_uncleared_byte {
                Some(last_uncleared_byte) => {
                    if last_uncleared_byte != (page_end - 1) {
                        // we have some cleared bytes at the end of this page
                        // dbg!(last_uncleared_byte + 1);
                        this.next_log_addr = last_uncleared_byte + 1;

                        if let Some(next_uncleared) = this.first_uncleared(this.next_log_addr)? {
                            // this can be in the middle of a message; start at the next one
                            match this.next_message_boundary(next_uncleared)? {
                                Some(next_boundary) => {
                                    this.oldest_log_addr = next_boundary + 1;
                                }
                                None => todo!(), // likely at the end of our memory
                            }
                        } else {
                            // the remainder of the memory is cleared
                            this.oldest_log_addr = 0;
                        }

                        break;
                    }
                }
                None => {
                    // dbg!(" end of flash?" );
                }
            }
        }

        Ok(this)
    }
}

const WORKING_BUF_SIZE: usize = 1000;

#[derive(Debug)]
enum CrossPageBoundary {
    FitsInCurrentPage,
    EndsOnPageBoundary { next_page_start_address: usize },
    NextPage { start_address: usize },
    BackToTheBeginning,
}

fn crosses_page_boundary<F>(flash: &F, start_address: usize, buf: &[u8]) -> CrossPageBoundary
where
    F: embedded_storage::nor_flash::NorFlash,
{
    let end_address = start_address + buf.len();

    assert!(end_address - start_address <= F::ERASE_SIZE);

    let ends_at_page_boundary = (end_address) % F::ERASE_SIZE == 0;
    let starts_at_page_boundary = start_address % F::ERASE_SIZE == 0;
    let crosses_page_boundary =
        (start_address / F::ERASE_SIZE) != ((end_address - 1) / F::ERASE_SIZE);

    if starts_at_page_boundary || crosses_page_boundary {
        if end_address > flash.capacity() {
            CrossPageBoundary::BackToTheBeginning
        } else {
            CrossPageBoundary::NextPage {
                start_address: (end_address / F::ERASE_SIZE) * F::ERASE_SIZE,
            }
        }
    } else if ends_at_page_boundary {
        CrossPageBoundary::EndsOnPageBoundary {
            next_page_start_address: if end_address == flash.capacity() {
                0
            } else {
                ((end_address + 1) / F::ERASE_SIZE) * F::ERASE_SIZE
            },
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
        println!("zeroing {} .. {}", start, end);
        for index in start..end {
            self.flash.write(index, &[0])?;
        }

        Ok(())
    }


    fn store_help(&mut self, bytes: &mut[u8])-> NvmLogResult<(), F::Error> {
        use CrossPageBoundary::*;
        match dbg!(crosses_page_boundary(&self.flash, self.next_log_addr as usize, bytes) ){
            FitsInCurrentPage => {
                // don't need to erase anything
                self.flash.write(self.next_log_addr, bytes)?;
                self.move_cursor_add(bytes.len() as u32, None)?;
            }
            EndsOnPageBoundary {
                next_page_start_address,
            } => {
                // we pad the current page with zeros
                let current = self.next_log_addr;

                assert!(next_page_start_address % F::ERASE_SIZE  == 0);
                
                self.write_zeros(current, next_page_start_address as u32)?;

                self.move_cursor_add(bytes.len() as _, None)?;

                return self.store_help(bytes);
            }
            NextPage { start_address } => {
                // pad the current page with zeros
                let current = self.next_log_addr;

                if current != start_address as u32 {
                    assert!(start_address % F::ERASE_SIZE  == 0);
                    
                    self.write_zeros(current, start_address as u32)?;

                    self.move_cursor_add(bytes.len() as _, None)?;
                }

                // we will (partially) write into the next page; we must erase it first
                let start_address = start_address as u32;
                let end_address = start_address + F::ERASE_SIZE as u32;
                self.flash.erase(start_address, end_address)?;

                self.flash.write(self.next_log_addr, bytes)?;
                self.move_cursor_add(bytes.len() as u32, None)?;
            }
            BackToTheBeginning => {
                // we pad the current page with zeros
                let current = self.next_log_addr;
                let next_page_start_address  = self.flash.capacity();

                dbg!(current , next_page_start_address);

                assert!(next_page_start_address % F::ERASE_SIZE  == 0);
                
                self.write_zeros(current, next_page_start_address  as u32)?;

                let start_address = 0u32;
                let end_address = start_address + F::ERASE_SIZE as u32;
                self.flash.erase(start_address, end_address)?;

                self.flash.write(0, bytes)?;
                self.move_cursor_absolute(bytes.len() as u32, Some(start_address..end_address))?;
            }
        }

        Ok(())
    }
}

impl<F: embedded_storage::nor_flash::ReadNorFlash, T> NvmLog<F, T> {
    /// The next_log_addr is moved forward by `added`. It may now be bigger
    /// than the `oldest_log_addr`, so it too needs to move forward to the
    /// start of the next log
    fn move_cursor_add(
        &mut self,
        added: u32,
        erased: Option<Range<u32>>,
    ) -> NvmLogResult<(), F::Error> {
        let new = self.next_log_addr + added;

        if self.next_log_addr <= self.oldest_log_addr && new > self.oldest_log_addr {
            self.skip_to_next_log(new)?;
        } else if let Some(range) = erased {
            if range.contains(&self.oldest_log_addr) {
                self.skip_to_next_log(range.end as u32)?;
            }
        }

        self.next_log_addr = new;

        Ok(())
    }

    fn move_cursor_absolute(
        &mut self,
        new: u32,
        erased: Option<Range<u32>>,
    ) -> NvmLogResult<(), F::Error> {
        if new > self.oldest_log_addr {
            self.skip_to_next_log(new)?;
        } else if let Some(range) = erased {
            if range.contains(&self.oldest_log_addr) {
                self.skip_to_next_log(range.end as u32)?;
            }
        }

        self.next_log_addr = new;

        Ok(())
    }

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

    fn skip_to_next_log_wrap(&mut self, start: u32) -> NvmLogResult<(), F::Error> {
        if start == 0 {
            // we've traversed the whole memory, but found nothing
            self.oldest_log_addr = self.next_log_addr;
            Ok(())
        } else {
            self.skip_to_next_log(0)
        }
    }

    fn skip_to_next_log(&mut self, start: u32) -> NvmLogResult<(), F::Error> {
        match self.next_message_boundary(start)? {
            None => self.skip_to_next_log_wrap(start),
            Some(boundary) => {
                // we've found a boundary, but still need to check that a message actually follows
                if boundary == self.flash.capacity() as u32 - 1 {
                    // the boundary is at the last valid address;
                    // no message can follow here, so check from the start
                    self.skip_to_next_log_wrap(start)
                } else {
                    match self.next_message_boundary(boundary + 1)? {
                        None => self.skip_to_next_log_wrap(start),
                        Some(_next_boundary) => {
                            // +1 because boundary is the NULL byte; next message starts 1 later
                            self.oldest_log_addr = boundary as u32 + 1;
                            Ok(())
                        }
                    }
                }
            }
        }
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

impl<'a, F: embedded_storage::nor_flash::ReadNorFlash, T: serde::de::DeserializeOwned>
    NvmLog<F, T>
{
    pub fn iter(&'a mut self) -> NvmLogIter<'a, F, T> {
        NvmLogIter {
            result_iter: self.result_iter(),
        }
    }

    pub fn result_iter(&'a mut self) -> NvmLogResultIter<'a, F, T> {
        let span = if self.oldest_log_addr < self.next_log_addr {
            Span::Contiguous {
                from: self.oldest_log_addr,
                to: self.next_log_addr,
            }
        } else {
            Span::BrokenUp {
                from: self.oldest_log_addr,
                to: self.next_log_addr,
            }
        };

        NvmLogResultIter {
            span,
            nvm_log: self,
        }
    }
}

enum Span {
    /// A contiguous chunk
    Contiguous { from: u32, to: u32 },
    /// The region wraps around somewhere
    BrokenUp { from: u32, to: u32 },
}

impl Span {
    fn is_empty(&self) -> bool {
        match self {
            Span::Contiguous { from, to } => from == to,
            Span::BrokenUp { from, to } => {
                assert!(from != to);
                false
            }
        }
    }

    fn start(&self) -> u32 {
        match self {
            Self::Contiguous { from, .. } | Self::BrokenUp { from, .. } => *from,
        }
    }

    fn step(&mut self, width: u32, capacity: u32) {
        match self {
            Self::Contiguous { from, .. } => {
                *from += width;
                assert!(*from <= capacity);
            }
            Self::BrokenUp { from, .. } => {
                *from += width;
                assert!(*from <= capacity);
            }
        }
    }

    fn wrap(&mut self) {
        match &self {
            Self::Contiguous { to, .. } => *self = Self::Contiguous { from: *to, to: *to },
            Self::BrokenUp { to, .. } => *self = Self::Contiguous { from: 0, to: *to },
        }
    }
}

pub struct NvmLogIter<'a, F, T> {
    result_iter: NvmLogResultIter<'a, F, T>,
}

impl<'a, F, T> Iterator for NvmLogIter<'a, F, T>
where
    F: embedded_storage::nor_flash::ReadNorFlash,
    T: serde::de::DeserializeOwned,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.result_iter.next()?.ok()
    }
}

pub struct NvmLogResultIter<'a, F, T> {
    nvm_log: &'a mut NvmLog<F, T>,
    span: Span,
}

impl<'a, F, T> Iterator for NvmLogResultIter<'a, F, T>
where
    F: embedded_storage::nor_flash::ReadNorFlash,
    T: serde::de::DeserializeOwned,
{
    type Item = NvmLogResult<T, F::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.span.is_empty() {
            return None;
        }

        let remaining_bytes = self.nvm_log.flash.capacity() - self.span.start() as usize;
        let remaining_bytes = remaining_bytes.min(WORKING_BUF_SIZE);

        let mut buf = [0xFF; WORKING_BUF_SIZE];
        let buf = &mut buf[..remaining_bytes];

        match self.nvm_log.flash.read(self.span.start(), buf) {
            Err(e) => Some(Err(NvmLogError::Flash(e))),
            Ok(()) => {
                match buf.iter().position(|x| *x == 0) {
                    None => {
                        // there is no message here, we need to go look at the start
                        self.span.wrap();
                        self.next()
                    }
                    Some(message_end) => {
                        let buf = &mut buf[..message_end];

                        let capacity = self.nvm_log.flash.capacity() as u32;
                        // +1 to skip the NULL byte
                        // +1 to skip the HEADER byte
                        // TODO skip if the header is inactive
                        self.span.step(message_end as u32 + 1, capacity);
                        match postcard::from_bytes_cobs(buf) {
                            Ok(e) => Some(Ok(e)),
                            Err(e) => Some(Err(NvmLogError::Postcard(e))),
                        }
                    }
                }
            }
        }
    }
}
