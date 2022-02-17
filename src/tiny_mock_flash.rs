#![cfg(feature = "std")]

use core::ops::Range;
use embedded_storage::nor_flash::{NorFlash, ReadNorFlash};

#[derive(Debug, Clone)]
struct MockFlash {
    writable: Vec<bool>,
    words: Vec<u8>,
}

impl Default for MockFlash {
    fn default() -> Self {
        Self::new()
    }
}

impl MockFlash {
    const PAGES: usize = 3;
    const BYTES_PER_WORD: usize = 1;

    const CAPACITY_WORDS: usize = Self::PAGES * Self::PAGE_WORDS;
    const CAPACITY_BYTES: usize = Self::CAPACITY_WORDS * Self::BYTES_PER_WORD;

    const PAGE_WORDS: usize = 8;
    const PAGE_BYTES: usize = Self::PAGE_WORDS * Self::BYTES_PER_WORD;

    pub fn new() -> Self {
        Self {
            writable: vec![true; Self::CAPACITY_WORDS],
            words: vec![u8::MAX; Self::CAPACITY_WORDS],
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

        #[allow(clippy::modulo_one)]
        if (offset % Self::BYTES_PER_WORD) != 0 {
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

        let start_word = range.start / Self::BYTES_PER_WORD;
        let end_word = (range.end + Self::BYTES_PER_WORD - 1) / Self::BYTES_PER_WORD;

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

    const READ_SIZE: usize = Self::BYTES_PER_WORD;

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
    const WRITE_SIZE: usize = Self::BYTES_PER_WORD;

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

        let range = from / Self::BYTES_PER_WORD..to / Self::BYTES_PER_WORD;
        for word_writable in self.writable[range].iter_mut() {
            *word_writable = true;
        }

        Ok(())
    }

    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        println!("Writing at offset {} {:?}", offset, bytes);
        let range = self.validate_write_operation(offset, bytes.len())?;

        let start_word = range.start / Self::BYTES_PER_WORD;
        let end_word = (range.end + Self::BYTES_PER_WORD - 1) / Self::BYTES_PER_WORD;

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
    use crate::NvmLog;
    // use std::assert_matches::assert_matches;

    #[test]
    fn double_write_gives_error() {
        let mut flash = MockFlash::new();

        flash.write(0, &[0xAB]).unwrap();

        assert!(matches!(
            flash.write(0, &[0xCD]),
            Err(MockFlashError::NotWritable(0))
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

    #[test]
    fn write_two_words() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..2 {
            nvm_log.store(i as u8).unwrap();
        }

        assert_eq!(
            &nvm_log.flash.words,
            &[
                1, 1, 0, 2, 1, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
                255, 255, 255, 255, 255,
            ]
        );

        assert_eq!(
            &nvm_log.flash.writable,
            &[
                false, false, false, false, false, false, true, true, true, true, true, true, true,
                true, true, true, true, true, true, true, true, true, true, true,
            ]
        );
    }

    #[test]
    fn write_two_words_erase_page() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..2 {
            nvm_log.store(i as u8).unwrap();
        }

        nvm_log.flash.erase(8, 16).unwrap();

        assert_eq!(
            &nvm_log.flash.words,
            &[
                1, 1, 0, 2, 1, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
                255, 255, 255, 255, 255,
            ]
        );

        assert_eq!(
            &nvm_log.flash.writable,
            &[
                false, false, false, false, false, false, true, true, true, true, true, true, true,
                true, true, true, true, true, true, true, true, true, true, true,
            ]
        );
    }

    #[test]
    fn write_three_words() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        // this will cross a page boundary
        for i in 0..3 {
            nvm_log.store(i as u8).unwrap();
        }

        assert_eq!(
            &nvm_log.flash.words,
            &[
                1, 1, 0, 2, 1, 0, 2, 2, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
                255, 255, 255, 255,
            ]
        );

        assert_eq!(
            &nvm_log.flash.writable,
            &[
                false, false, false, false, false, false, false, false, false, true, true, true,
                true, true, true, true, true, true, true, true, true, true, true, true,
            ]
        );
    }

    #[test]
    fn write_eight_words() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        // this will fill up all memory, but not wrap around yet
        for i in 0..8 {
            nvm_log.store(i as u8).unwrap();
        }

        assert_eq!(
            &nvm_log.flash.words,
            &[1, 1, 0, 2, 1, 0, 2, 2, 0, 2, 3, 0, 2, 4, 0, 2, 5, 0, 2, 6, 0, 2, 7, 0,]
        );

        assert_eq!(
            &nvm_log.flash.writable,
            &[
                false, false, false, false, false, false, false, false, false, false, false, false,
                false, false, false, false, false, false, false, false, false, false, false, false,
            ]
        );
    }

    #[test]
    fn write_nine_words() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        // this will wrap around
        for i in 0..9 {
            nvm_log.store(i as u8).unwrap();
            dbg!(&nvm_log.flash);
        }

        assert_eq!(
            &nvm_log.flash.words,
            &[2, 8, 0, 255, 255, 255, 255, 255, 0, 2, 3, 0, 2, 4, 0, 2, 5, 0, 2, 6, 0, 2, 7, 0]
        );

        assert_eq!(
            &nvm_log.flash.writable,
            &[
                false, false, false, true, true, true, true, true, false, false, false, false,
                false, false, false, false, false, false, false, false, false, false, false, false,
            ]
        );

        // next-oldest message is the first message on the second page
        assert_eq!(nvm_log.oldest_log_addr, 9);
    }

    #[test]
    fn read_middle_to_back() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..3 {
            nvm_log.store(i as u8).unwrap();
            dbg!(&nvm_log);
        }

        let it = nvm_log.iter();

        let messages: Vec<_> = it.collect();

        assert_eq!(vec![0, 1, 2], messages);
    }

    #[test]
    fn read_full() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..8 {
            nvm_log.store(i as u8).unwrap();
        }

        let it = nvm_log.iter();

        let messages: Vec<_> = it.collect();

        assert_eq!(vec![0, 1, 2, 3, 4, 5, 6, 7], messages);
    }

    #[test]
    fn read_disjoint() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..9 {
            nvm_log.store(i as u8).unwrap();
        }

        let it = nvm_log.iter();

        let messages: Vec<_> = it.collect();

        assert_eq!(vec![3, 4, 5, 6, 7, 8], messages);
    }

    #[test]
    fn foobar() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..9 {
            nvm_log.store(i as u8).unwrap();
        }

        let it = nvm_log.iter();

        let messages: Vec<_> = it.collect();

        dbg!(messages);
    }

    // oldest_log_addr can be in erased page
}
