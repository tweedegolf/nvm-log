#![cfg(feature = "std")]

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

pub struct MockFlash {
    writable: Vec<Writable>,
    words: Vec<u32>,
}

impl Default for MockFlash {
    fn default() -> Self {
        Self::new()
    }
}

impl MockFlash {
    const PAGES: usize = 3; // 256;
    const BYTES_PER_WORD: usize = 4;

    const CAPACITY_WORDS: usize = Self::PAGES * Self::PAGE_WORDS;
    const CAPACITY_BYTES: usize = Self::CAPACITY_WORDS * Self::BYTES_PER_WORD;

    const PAGE_WORDS: usize = 32; // 1024;
    const PAGE_BYTES: usize = Self::PAGE_WORDS * Self::BYTES_PER_WORD;

    pub fn new() -> Self {
        Self {
            writable: vec![T; Self::CAPACITY_WORDS],
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
            if *writable == Writable::N {
                return Err(MockFlashError::NotWritable(address as u32));
            }
        }

        Ok(range)
    }
}

#[derive(Debug, Clone)]
pub enum MockFlashError {
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
    const READ_SIZE: usize = 1;

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
            *word_writable = T;
        }

        Ok(())
    }

    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        let range = self.validate_write_operation(offset, bytes.len())?;

        if bytes.len() % Self::WRITE_SIZE != 0 {
            panic!("any write must be a multiple of Self::WRITE_SIZE bytes");
        }

        let start_word = range.start / Self::BYTES_PER_WORD;
        let end_word = (range.end + Self::BYTES_PER_WORD - 1) / Self::BYTES_PER_WORD;

        for (target, source) in self.as_bytes_mut()[range].iter_mut().zip(bytes.iter()) {
            *target &= *source;
        }

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
    use arrayvec::ArrayString;
    use serde::{Deserialize, Serialize};

    #[test]
    fn triple_write_gives_error() {
        let mut flash = MockFlash::new();

        flash.write(0x100, &[0xAB, 0, 0, 0]).unwrap();
        flash.write(0x100, &[0xAB, 0, 0, 0]).unwrap();

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
            Err(MockFlashError::NotAligned)
        ))
    }

    #[test]
    fn misaligned_write_gives_error() {
        let mut flash = MockFlash::new();

        assert!(matches!(
            flash.write(1, &[0xCD]),
            Err(MockFlashError::NotAligned)
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

    /// Unix time in milliseconds
    #[derive(Clone, Copy, Deserialize, Serialize, Debug, PartialEq)]
    pub struct DateTime(i64);

    #[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq)]
    pub enum TickToUnixResult {
        /// The tick time was converted to a unix time
        Success(DateTime),
        /// The system clock has not been synchronized with the network
        /// so it is impossible to give an accurate date time
        NotSynchronized,
    }
    #[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
    pub enum LogMessage {
        /// An error occurred while reading a message from the NVM logs.
        /// Contains the start address of the message.
        NvmLogReadError(u32),
        /// The LTE-M/GPS modem crashed
        ModemCrash,
        /// The device just booted
        DeviceBoot,
        /// A resetreason was found
        ResetCode(ArrayString<64>),
        /// The LTE modem timed out for some reason
        LteTimeout,
        /// There was a panic.
        /// We need to limit the bytes to stay within [crate::nvm_log::WORKING_BUF_SIZE].
        Panic(ArrayString<192>),
        /// We woke up from movement
        MovementReported,
        /// The time was not synchronized with the network.
        /// For sending messages to the server, we rely on the time being synchronized.
        TimeNotSynchronized,
        /// The firmware was updated to a new version
        FirmwareUpdated,
        // Adding new variants is OK, but do not alter their value
    }
    #[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
    pub struct LogEntry {
        pub msg: LogMessage,
        pub timestamp: TickToUnixResult,
    }

    #[test]
    fn decode_our_logs_from_memory() {
        use LogMessage::*;
        use TickToUnixResult::*;

        const MEMORY: [u8; 40] = [
            192, 3, 2, 1, 0, 0, 0, 0, 192, 12, 3, 8, 87, 97, 116, 99, 104, 100, 111, 103, 1, 0, 0,
            0, 192, 2, 6, 7, 156, 95, 149, 64, 127, 1, 1, 1, 0, 0, 0, 0,
        ];

        let memory_u32: [u32; MEMORY.len() / 4] = unsafe { core::mem::transmute(MEMORY) };

        let mut flash = MockFlash::new();
        flash.words[..MEMORY.len() / 4].copy_from_slice(&memory_u32);

        let nvm_log: NvmLog<MockFlash, LogEntry> = NvmLog::new_infer_position(flash).unwrap();

        let messages: Vec<_> = nvm_log.result_iter().unwrap().flatten().collect();
        let expected: Vec<LogEntry> = vec![
            LogEntry {
                msg: DeviceBoot,
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: ResetCode(ArrayString::from("Watchdog").unwrap()),
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: MovementReported,
                timestamp: Success(DateTime(1646056005532)),
            },
        ];

        assert_eq!(expected, messages);
    }

    #[test]
    fn decode_our_logs_after_writing() {
        use LogMessage::*;
        use TickToUnixResult::*;

        let flash = MockFlash::new();
        let mut nvm_log: NvmLog<MockFlash, LogEntry> = NvmLog::new_infer_position(flash).unwrap();

        let expected: Vec<LogEntry> = vec![
            LogEntry {
                msg: DeviceBoot,
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: ResetCode(ArrayString::from("Watchdog").unwrap()),
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: MovementReported,
                timestamp: Success(DateTime(1646056005532)),
            },
        ];

        for msg in expected.clone() {
            nvm_log.store(msg).unwrap();
        }

        let messages: Vec<_> = nvm_log.result_iter().unwrap().flatten().collect();

        assert_eq!(expected, messages);
    }

    #[test]
    fn iterate_erase_iterate() {
        use LogMessage::*;
        use TickToUnixResult::*;

        let flash = MockFlash::new();
        let mut nvm_log: NvmLog<MockFlash, LogEntry> = NvmLog::new_infer_position(flash).unwrap();

        let messages: Vec<LogEntry> = vec![
            LogEntry {
                msg: DeviceBoot,
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: ResetCode(ArrayString::from("Watchdog").unwrap()),
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: MovementReported,
                timestamp: Success(DateTime(1646056005532)),
            },
        ];

        for msg in messages.clone() {
            nvm_log.store(msg).unwrap();
        }

        let start_position = nvm_log.current_position();
        let mut it = nvm_log.result_iter().unwrap();
        let first: Vec<_> = (&mut it).flatten().collect();

        let mut nvm_log = it.free();

        let slice = &nvm_log.flash.words[..8];
        let slice2 =
            unsafe { core::slice::from_raw_parts(slice.as_ptr() as *const u8, slice.len() * 4) };

        dbg!(slice2);

        nvm_log.deactivate_up_to_position(&start_position).unwrap();

        let slice = &nvm_log.flash.words[..8];
        let slice2 =
            unsafe { core::slice::from_raw_parts(slice.as_ptr() as *const u8, slice.len() * 4) };

        dbg!(slice2);

        let it = nvm_log.result_iter().unwrap();
        let second: Vec<_> = it.flatten().collect();

        assert_eq!(first, messages);
        assert_eq!(second, vec![]);
    }

    #[test]
    fn find_the_start_after_erase() {
        use LogMessage::*;
        use TickToUnixResult::*;

        const MEMORY: [u8; 256] = [
            128, 3, 2, 1, 0, 0, 0, 0, 128, 15, 3, 11, 83, 121, 115, 82, 101, 115, 101, 116, 82,
            101, 113, 1, 0, 0, 0, 0, 128, 3, 2, 1, 0, 0, 0, 0, 128, 17, 3, 13, 87, 97, 107, 101,
            117, 112, 70, 114, 111, 109, 79, 102, 102, 1, 0, 0, 128, 2, 6, 7, 250, 254, 196, 69,
            127, 1, 1, 1, 0, 0, 0, 0, 128, 3, 2, 1, 0, 0, 0, 0, 128, 12, 3, 8, 82, 101, 115, 101,
            116, 80, 105, 110, 1, 0, 0, 0, 128, 2, 6, 7, 31, 244, 197, 69, 127, 1, 1, 1, 0, 0, 0,
            0, 192, 3, 2, 1, 0, 0, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255,
        ];

        let memory_u32: [u32; MEMORY.len() / 4] = unsafe { core::mem::transmute(MEMORY) };

        let mut flash = MockFlash::new();
        flash.words[..MEMORY.len() / 4].copy_from_slice(&memory_u32);

        let nvm_log: NvmLog<MockFlash, LogEntry> = NvmLog::new_infer_position(flash).unwrap();

        let messages: Vec<_> = nvm_log.result_iter().unwrap().flatten().collect();

        let expected = vec![LogEntry {
            msg: DeviceBoot,
            timestamp: NotSynchronized,
        }];

        assert_eq!(expected, messages);
    }

    #[test]
    fn fill_it_up() {
        use LogMessage::*;
        use TickToUnixResult::*;

        let flash = MockFlash::new();
        let mut nvm_log: NvmLog<MockFlash, LogEntry> = NvmLog::new_infer_position(flash).unwrap();

        let messages: Vec<LogEntry> = vec![
            LogEntry {
                msg: DeviceBoot,
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: ResetCode(ArrayString::from("Watchdog").unwrap()),
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: MovementReported,
                timestamp: Success(DateTime(1646056005532)),
            },
        ];

        for msg in messages.iter().cycle().take(10) {
            nvm_log.store(msg.clone()).unwrap();
        }

        let position = nvm_log.current_position();

        // this will wrap around
        for msg in messages.iter().cycle().take(5) {
            nvm_log.store(msg.clone()).unwrap();
        }

        nvm_log.deactivate_up_to_position(&position).unwrap();

        let messages: Vec<_> = nvm_log.result_iter().unwrap().flatten().collect();

        let expected: Vec<LogEntry> = vec![
            LogEntry {
                msg: DeviceBoot,
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: ResetCode(ArrayString::from("Watchdog").unwrap()),
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: MovementReported,
                timestamp: Success(DateTime(1646056005532)),
            },
            LogEntry {
                msg: DeviceBoot,
                timestamp: NotSynchronized,
            },
            LogEntry {
                msg: ResetCode(ArrayString::from("Watchdog").unwrap()),
                timestamp: NotSynchronized,
            },
        ];

        assert_eq!(messages, expected)
    }

    #[test]
    fn erase_empty() {
        let mut nvm_log: NvmLog<MockFlash, u8> = NvmLog::new(MockFlash::new());

        let position = nvm_log.current_position();

        nvm_log.deactivate_up_to_position(&position).unwrap();
    }
}
