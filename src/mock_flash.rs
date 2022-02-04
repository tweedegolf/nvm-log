#![cfg(feature = "std")]

use core::ops::Range;
use embedded_storage::nor_flash::{NorFlash, ReadNorFlash};

struct MockFlash {
    writable: Vec<bool>,
    words: Vec<u32>,
}

impl MockFlash {
    const PAGES: usize = 256;
    const BYTES_PER_WORD: usize = 4;

    const CAPACITY_WORDS: usize = Self::PAGES * Self::PAGE_WORDS;
    const CAPACITY_BYTES: usize = Self::CAPACITY_WORDS * Self::BYTES_PER_WORD;

    const PAGE_WORDS: usize = 1024;
    const PAGE_BYTES: usize = Self::PAGE_WORDS * Self::BYTES_PER_WORD;

    pub fn new() -> Self {
        Self {
            writable: vec![true; Self::CAPACITY_WORDS],
            words: vec![u32::MAX; Self::CAPACITY_WORDS],
        }
    }

    fn as_bytes(&self) -> &[u8] {
        let ptr_words = self.words.as_ptr();
        let ptr_bytes = ptr_words as *const u8;
        unsafe { core::slice::from_raw_parts(ptr_bytes, Self::CAPACITY_BYTES) }
    }

    fn as_bytes_mut(&mut self) -> &mut [u8] {
        let ptr_words = self.words.as_mut_ptr();
        let ptr_bytes = ptr_words as *mut u8;
        unsafe { core::slice::from_raw_parts_mut(ptr_bytes, Self::CAPACITY_BYTES) }
    }

    fn validate_read_operation(offset: u32, length: usize) -> Result<Range<usize>, MockFlashError> {
        let offset = offset as usize;
        if (offset % 4) != 0 {
            Err(MockFlashError::Misaligned)
        } else if offset > MockFlash::CAPACITY_BYTES || offset + length > MockFlash::CAPACITY_BYTES
        {
            Err(MockFlashError::OutOfBounds)
        } else {
            Ok(offset..(offset + length))
        }
    }

    fn validate_write_operation(
        &self,
        offset: u32,
        length: usize,
    ) -> Result<Range<usize>, MockFlashError> {
        let range = Self::validate_read_operation(offset, length)?;

        let start_word = range.start / 4;
        let end_word = (range.end + 4 - 1) / 4;

        let slice = &self.writable[start_word..end_word];
        let it = (range.start..range.end).zip(slice.iter());
        for (address, writable) in it {
            if !writable {
                return Err(MockFlashError::NotWritable(address as u32));
            }
        }

        Ok(range)
    }
}

#[derive(Debug)]
enum MockFlashError {
    OutOfBounds,
    Misaligned,
    NotWritable(u32),
}

impl ReadNorFlash for MockFlash {
    type Error = MockFlashError;

    const READ_SIZE: usize = 4;

    fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
        let range = Self::validate_read_operation(offset, bytes.len())?;

        bytes.copy_from_slice(&self.as_bytes()[range]);

        Ok(())
    }

    fn capacity(&self) -> usize {
        Self::CAPACITY_BYTES
    }
}

impl NorFlash for MockFlash {
    const WRITE_SIZE: usize = 4;

    const ERASE_SIZE: usize = Self::PAGE_BYTES;

    fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error> {
        let from = from as usize;
        let to = to as usize;

        assert!(from <= to);

        if to > Self::CAPACITY_BYTES {
            return Err(MockFlashError::OutOfBounds);
        }

        if from % Self::PAGE_BYTES != 0 || to % Self::PAGE_BYTES != 0 {
            return Err(MockFlashError::Misaligned);
        }

        for byte in self.as_bytes_mut()[from..to].iter_mut() {
            *byte = u8::MAX;
        }

        for word_writable in self.writable[from / 4..to / 4].iter_mut() {
            *word_writable = true;
        }

        Ok(())
    }

    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        let range = self.validate_write_operation(offset, bytes.len())?;

        let start_word = range.start / 4;
        let end_word = (range.end + 4 - 1) / 4;

        self.as_bytes_mut()[range].copy_from_slice(bytes);

        for word_writable in self.writable[start_word..end_word].iter_mut() {
            *word_writable = false;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    // use std::assert_matches::assert_matches;

    #[test]
    fn double_write_gives_error() {
        let mut flash = MockFlash::new();

        flash.write(0x100, &[0xAB]).unwrap();

        assert!(matches!(
            flash.write(0x100, &[0xCD]),
            Err(MockFlashError::NotWritable(0x100))
        ))
    }

    #[test]
    fn misaligned_read_gives_error() {
        let mut flash = MockFlash::new();

        let mut output = [0; 1];

        assert!(matches!(
            flash.read(1, &mut output),
            Err(MockFlashError::Misaligned)
        ))
    }

    #[test]
    fn misaligned_write_gives_error() {
        let mut flash = MockFlash::new();

        assert!(matches!(
            flash.write(1, &[0xCD]),
            Err(MockFlashError::Misaligned)
        ))
    }

    #[test]
    fn out_of_bounds_read_gives_error() {
        let mut flash = MockFlash::new();

        let mut output = [0; 1];

        assert!(matches!(
            flash.read(MockFlash::CAPACITY_BYTES as u32 + 4, &mut output),
            Err(MockFlashError::OutOfBounds)
        ))
    }

    #[test]
    fn out_of_bounds_write_gives_error() {
        let mut flash = MockFlash::new();

        assert!(matches!(
            flash.write(MockFlash::CAPACITY_BYTES as u32 + 4, &[0xCD]),
            Err(MockFlashError::OutOfBounds)
        ))
    }
}
