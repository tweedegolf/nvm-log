#![cfg(test)]
use crate::mock_flash::{MockFlashBase, Writable};
use crate::NvmLog;

use arrayvec::ArrayString;
use serde::{Deserialize, Serialize};

// from memory.x
// APPLICATION_LOGS_FLASH   : ORIGIN = 0x000F0000, LENGTH = 28K
const LOGS_LENGTH: usize = 28 * 1024;

const PAGES: usize = LOGS_LENGTH / (PAGE_WORDS * BYTES_PER_WORD);
const BYTES_PER_WORD: usize = 4;
const PAGE_WORDS: usize = 1024;
type Flash = MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>;

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
fn cannot_find_log_position() {
    const DUMP: &[u8] = include_bytes!("dumps/cannot-find-log-position.logs.bin");

    let log_bytes = DUMP;
    assert!(log_bytes.len() % 4 == 0);

    let log_words = unsafe {
        std::slice::from_raw_parts(log_bytes.as_ptr() as *const u32, log_bytes.len() / 4)
    };

    let flash = Flash {
        words: log_words.to_vec(),
        writable: vec![Writable::T; log_words.len()],
    };

    let nvm_log: NvmLog<Flash, LogEntry> = NvmLog::new_infer_position(flash).unwrap();

    assert_eq!(nvm_log.current_position().next_log_addr, 8284);

    let it = nvm_log.result_iter().unwrap();

    let logs: Vec<_> = it.map(|x| x.unwrap()).collect();

    // messages that are important enough to send back to the server,
    // even if the server did not explicitly ask for logs.
    let is_important_log_msg = |msg: &LogMessage| {
        use LogMessage::*;

        match msg {
            NvmLogReadError(_) => {
                // considering this message important creates a feedback loop where we read the
                // logs, notice there is an error, log that error, and then there is a new
                // important log message, so we would send the logs again.
                false
            }
            ModemCrash => true,
            DeviceBoot => false,
            ResetCode(_) => true,
            LteTimeout => false,
            TimeNotSynchronized => false,
            Panic(_) => true,
            MovementReported => false,
            FirmwareUpdated => false,
        }
    };

    assert!(logs.iter().any(|e| is_important_log_msg(&e.msg)));
}
