#![cfg(feature = "std")]

use crate::HEADER_ACTIVE;
use core::ops::Range;
use embedded_storage::nor_flash::{
    ErrorType, MultiwriteNorFlash, NorFlash, NorFlashError, NorFlashErrorKind, ReadNorFlash,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Writable {
    /// Twice
    T,
    /// Once (can only convert 1 bits to 0
    O,
    /// Never (must be cleared before being writable again)
    N,
}

use Writable::*;

#[derive(Debug, Clone)]
struct MockFlash {
    writable: Vec<Writable>,
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
            writable: vec![T; Self::CAPACITY_WORDS],
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
            Err(MockFlashError::NotAligned)
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
            if let Writable::N = writable {
                return Err(MockFlashError::NotWritable(address as u32));
            }
        }

        Ok(range)
    }
}

#[derive(Debug)]
enum MockFlashError {
    OutOfBounds,
    NotAligned,
    NotWritable(u32),
}

impl NorFlashError for MockFlashError {
    fn kind(&self) -> NorFlashErrorKind {
        match self {
            MockFlashError::OutOfBounds => NorFlashErrorKind::OutOfBounds,
            MockFlashError::NotAligned => NorFlashErrorKind::NotAligned,
            MockFlashError::NotWritable(_) => NorFlashErrorKind::Other,
        }
    }
}

impl ErrorType for MockFlash {
    type Error = MockFlashError;
}

impl ReadNorFlash for MockFlash {
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

impl MultiwriteNorFlash for MockFlash {}

impl NorFlash for MockFlash {
    const WRITE_SIZE: usize = Self::BYTES_PER_WORD;

    const ERASE_SIZE: usize = Self::PAGE_BYTES;

    fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error> {
        println!("erasing {} .. {}", from, to);
        let from = from as usize;
        let to = to as usize;

        assert!(from <= to);

        if to > Self::CAPACITY_BYTES {
            return Err(MockFlashError::OutOfBounds);
        }

        if from % Self::PAGE_BYTES != 0 || to % Self::PAGE_BYTES != 0 {
            return Err(MockFlashError::NotAligned);
        }

        for byte in self.as_bytes_mut()[from..to].iter_mut() {
            *byte = u8::MAX;
        }

        let range = from / Self::BYTES_PER_WORD..to / Self::BYTES_PER_WORD;
        for word_writable in self.writable[range].iter_mut() {
            *word_writable = Writable::T;
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
            *word_writable = match *word_writable {
                Writable::T => Writable::O,
                Writable::O => Writable::N,
                Writable::N => Writable::N,
            };
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
    fn double_write_is_fine() {
        let mut flash = MockFlash::new();

        flash.write(0, &[0xAB]).unwrap();

        assert!(matches!(flash.write(0, &[0xCD]), Ok(_)))
    }

    #[test]
    fn triple_write_gives_error() {
        let mut flash = MockFlash::new();

        flash.write(0, &[0xAB]).unwrap();
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
    fn write_words_2() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..2 {
            nvm_log.store(i as u8).unwrap();
        }

        assert_eq!(
            &nvm_log.flash.words,
            &[
                HEADER_ACTIVE,
                1,
                1,
                0,
                0,
                0,
                0,
                0,
                HEADER_ACTIVE,
                2,
                1,
                0,
                255,
                255,
                255,
                255,
                255,
                255,
                255,
                255,
                255,
                255,
                255,
                255,
            ]
        );

        let mut flags = [T; 24];

        for item in flags.iter_mut().take(12) {
            *item = O;
        }

        assert_eq!(&nvm_log.flash.writable, &flags,);
    }

    /*
    #[test]
    fn write_words_3() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..3 {
            nvm_log.store(i as u8).unwrap();
        }

        assert_eq!(
            &nvm_log.flash.words,
            &[
                HEADER_ACTIVE,
                1,
                1,
                0,
                0,
                0,
                0,
                0,
                HEADER_ACTIVE,
                2,
                1,
                0,
                0,
                0,
                0,
                0,
                HEADER_ACTIVE,
                2,
                2,
                0,
                255,
                255,
                255,
                255,
            ]
        );

        let mut flags = [true; 24];

        for i in 0..20 {
            flags[i] = false;
        }

        assert_eq!(&nvm_log.flash.writable, &flags,);
    }

    #[test]
    fn write_words_4() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..4 {
            nvm_log.store(i as u8).unwrap();
        }

        assert_eq!(
            &nvm_log.flash.words,
            &[
                HEADER_ACTIVE,
                1,
                1,
                0,
                0,
                0,
                0,
                0,
                HEADER_ACTIVE,
                2,
                1,
                0,
                0,
                0,
                0,
                0,
                HEADER_ACTIVE,
                2,
                2,
                0,
                255,
                255,
                255,
                255,
            ]
        );

        let mut flags = [true; 24];

        for i in 0..20 {
            flags[i] = false;
        }

        assert_eq!(&nvm_log.flash.writable, &flags,);
    }

    #[test]
    fn write_words_5() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..5 {
            nvm_log.store(i as u8).unwrap();
        }

        assert_eq!(
            &nvm_log.flash.words,
            &[
                192, 1, 1, 0, 192, 2, 1, 0, 192, 2, 2, 0, 192, 2, 3, 0, 192, 2, 4, 0, 255, 255,
                255, 255
            ]
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
    fn write_words_6() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        // this will fill up all memory, but not wrap around yet
        // it will however clear the next (i.e. the first) page
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
    */

    #[test]
    fn read_1() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..1 {
            nvm_log.store(i as u8).unwrap();
        }

        let messages: Vec<_> = nvm_log.iter().collect();

        assert_eq!(vec![0], messages);
    }

    #[test]
    fn read_2() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..2 {
            nvm_log.store(i as u8).unwrap();
        }

        let messages: Vec<_> = nvm_log.iter().collect();

        assert_eq!(vec![0, 1], messages);
    }

    #[test]
    fn read_3() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..3 {
            nvm_log.store(i as u8).unwrap();
        }

        let messages: Vec<_> = nvm_log.iter().collect();

        assert_eq!(vec![0, 1, 2], messages);
    }

    #[test]
    fn write_4_read_3() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..4 {
            nvm_log.store(i as u8).unwrap();
        }

        dbg!(&nvm_log.flash.words);

        let messages: Vec<_> = nvm_log.iter().collect();

        assert_eq!(vec![1, 2, 3], messages);
    }

    #[test]
    fn write_1_erase_1() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..1 {
            nvm_log.store(i as u8).unwrap();
        }

        let position = nvm_log.current_position();
        nvm_log.erase_up_to_position(&position).unwrap();

        let messages: Vec<u8> = nvm_log.iter().collect();
        let expected: Vec<u8> = vec![];

        assert_eq!(expected, messages);
    }

    #[test]
    fn write_2_erase_2() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..2 {
            nvm_log.store(i as u8).unwrap();
        }

        let position = nvm_log.current_position();
        nvm_log.erase_up_to_position(&position).unwrap();

        let messages: Vec<u8> = nvm_log.iter().collect();
        let expected: Vec<u8> = vec![];

        assert_eq!(expected, messages);
    }

    #[test]
    fn write_2_erase_1() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        nvm_log.store(0).unwrap();
        let position = nvm_log.current_position();
        nvm_log.store(1).unwrap();

        nvm_log.erase_up_to_position(&position).unwrap();

        let messages: Vec<u8> = nvm_log.iter().collect();
        let expected: Vec<u8> = vec![1];

        assert_eq!(expected, messages);
    }

    #[test]
    fn write_3_erase_1() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        nvm_log.store(0).unwrap();
        let position = nvm_log.current_position();
        nvm_log.store(1).unwrap();
        nvm_log.store(2).unwrap();

        nvm_log.erase_up_to_position(&position).unwrap();

        let messages: Vec<u8> = nvm_log.iter().collect();
        let expected: Vec<u8> = vec![1, 2];

        assert_eq!(expected, messages);
    }

    fn recover_n(n: usize) {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..n {
            nvm_log.store(i as u8).unwrap();
        }

        let old = nvm_log.next_log_addr;

        let (mut flash, _) = nvm_log.free();

        let new_position = NvmLog::<MockFlash, u8>::restore_from_flash(&mut flash).unwrap();
        let nvm_log = NvmLog::<MockFlash, u8>::new_at_position(flash, new_position);

        let new = new_position.next_log_addr;

        assert_eq!(old, new, "{:?}", nvm_log.flash.words);
    }

    #[test]
    fn recover_0() {
        recover_n(0);
    }

    #[test]
    fn recover_1() {
        recover_n(1);
    }

    #[test]
    fn recover_2() {
        recover_n(2);
    }

    #[test]
    fn recover_many() {
        for n in 0..20 {
            println!(" {}", n);
            recover_n(n);
        }
    }
    /*

    #[test]
    fn foobar() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        for i in 0..11 {
            nvm_log.store(i as u8).unwrap();
        }

        dbg!(nvm_log.oldest_log_addr, nvm_log.next_log_addr);
        let flash = nvm_log.free();

        let new: NvmLog<MockFlash, u8> = NvmLog::restore_from_flash(flash).unwrap();
        dbg!(new.oldest_log_addr, new.next_log_addr);
        dbg!(&new.flash.words);
    }

    // oldest_log_addr can be in erased page
    */
}
