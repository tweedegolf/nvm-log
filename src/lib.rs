#![cfg_attr(all(not(test), not(feature = "std")), no_std)]

use embedded_storage::ReadStorage;

pub mod mock_flash;
pub mod tiny_mock_flash;

#[derive(Debug)]
pub struct NvmLog<F, T> {
    oldest_log_addr: u32,
    next_log_addr: u32,
    flash: F,
    _marker: core::marker::PhantomData<T>,
}

pub struct NvmLogPosition {
    oldest_log_addr: u32,
    next_log_addr: u32,
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

    pub fn current_postition(&self) -> NvmLogPosition {
        NvmLogPosition {
            oldest_log_addr: self.oldest_log_addr,
            next_log_addr: self.next_log_addr,
        }
    }

    pub fn erase_up_to_position(&mut self, position: &NvmLogPosition) {
        self.oldest_log_addr = position.next_log_addr;
    }
}

const WORKING_BUF_SIZE: usize = 1000;

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
    } else {
        CrossPageBoundary::FitsInCurrentPage
    }
}

impl<F: embedded_storage::nor_flash::NorFlash, T: serde::Serialize> NvmLog<F, T> {
    pub fn store(&mut self, value: T) -> Result<(), F::Error> {
        let mut buf = [0u8; WORKING_BUF_SIZE];
        let bytes = postcard::to_slice_cobs(&value, &mut buf).unwrap();

        use CrossPageBoundary::*;
        match crosses_page_boundary(&self.flash, self.next_log_addr as usize, bytes) {
            FitsInCurrentPage => {
                // don't need to erase anything
                self.flash.write(self.next_log_addr, bytes)?;
                self.move_cursor_add(bytes.len() as u32)?;
                Ok(())
            }
            NextPage { start_address } => {
                // we will (partially) write into the next page; we must erase it first
                self.flash
                    .erase(start_address as u32, (start_address + F::ERASE_SIZE) as u32)?;

                self.flash.write(self.next_log_addr, bytes)?;
                self.move_cursor_add(bytes.len() as u32)?;
                Ok(())
            }
            BackToTheBeginning => {
                // NOTE the final bytes in the last page stay 0xFF
                // we rely on this fact to see if there are messages
                // in a given piece of memory (messages always end
                // with a NULL byte when encoded with Cobs)
                self.flash.erase(0, F::ERASE_SIZE as u32)?;

                self.flash.write(0, bytes)?;
                self.move_cursor_absolute(bytes.len() as u32)?;
                Ok(())
            }
        }
    }
}

impl<F: embedded_storage::nor_flash::ReadNorFlash, T> NvmLog<F, T> {
    /// The next_log_addr is moved forward by `added`. It may now be bigger
    /// than the `oldest_log_addr`, so it too needs to move forward to the
    /// start of the next log
    fn move_cursor_add(&mut self, added: u32) -> Result<(), F::Error> {
        let new = self.next_log_addr + added;
        if self.next_log_addr <= self.oldest_log_addr && new > self.oldest_log_addr {
            self.move_cursor_absolute(new)
        } else {
            self.next_log_addr = new;
            Ok(())
        }
    }

    fn move_cursor_absolute(&mut self, new: u32) -> Result<(), F::Error> {
        let mut next_oldest_log = 0;

        if new >= self.oldest_log_addr {
            for offset in new as usize..self.flash.capacity() {
                let mut word = [0];
                self.flash.read(offset as u32, &mut word)?;

                // a NULL bytes is the COPS message sentinal (end) value
                if word[0] == 0 {
                    next_oldest_log = (offset + 1) % self.flash.capacity();
                    break;
                }
            }

            self.oldest_log_addr = next_oldest_log as u32;
        }

        self.next_log_addr = new;

        Ok(())
    }
}

pub struct NvmLogIter<'a, F, T> {
    nvm_log: &'a mut NvmLog<F, T>,
    span: Span,
}

impl<'a, F: embedded_storage::nor_flash::ReadNorFlash, T: serde::de::DeserializeOwned>
    NvmLog<F, T>
{
    pub fn iter(&'a mut self) -> NvmLogIter<'a, F, T> {
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

        NvmLogIter {
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
        if let Self::Contiguous { from, to } = self {
            from == to
        } else {
            false
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

impl<'a, F: embedded_storage::nor_flash::ReadNorFlash, T: serde::de::DeserializeOwned> Iterator
    for NvmLogIter<'a, F, T>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.span.is_empty() {
            return None;
        }

        let remaining_bytes = self.nvm_log.flash.capacity() - self.span.start() as usize;
        let remaining_bytes = remaining_bytes.min(WORKING_BUF_SIZE);

        let mut buf = [0xFF; WORKING_BUF_SIZE];
        let buf = &mut buf[..remaining_bytes];

        match self.nvm_log.flash.read(self.span.start(), buf) {
            Err(_e) => {
                dbg!("flash read error");
                None
            }
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
                        self.span.step(message_end as u32 + 1, capacity);
                        match postcard::from_bytes_cobs(buf) {
                            Ok(e) => Some(e),
                            Err(_e) => None,
                        }
                    }
                }
            }
        }
    }
}
