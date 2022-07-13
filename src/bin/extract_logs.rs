fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    println!("{:?}", args);

    let argument = &args[1];

    let mut path = std::path::PathBuf::from(argument);
    let dump_bytes = std::fs::read(&path)?;

    let log_bytes = &dump_bytes[LOGS_START..][..LOGS_LENGTH];
    assert!(log_bytes.len() % 4 == 0);

    path.set_extension("logs.bin");

    std::fs::write(&path, log_bytes)
}

// from memory.x
// APPLICATION_LOGS_FLASH   : ORIGIN = 0x000F0000, LENGTH = 28K
const LOGS_START: usize = 0x000F0000;
const LOGS_LENGTH: usize = 28 * 1024;
