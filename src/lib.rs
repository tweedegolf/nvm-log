#![cfg_attr(all(not(test), not(feature = "std")), no_std)]

pub mod mock_flash;

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

    pub fn erase_up_to_position(&mut self, position: &NvmLogPosition) -> Result<(), ()> {
        todo!()
    }
}

impl<F: embedded_storage::nor_flash::NorFlash, T: serde::Serialize> NvmLog<F, T> {
    fn store<const N: usize>(&mut self, value: T) -> Result<(), F::Error> {
        todo!()
    }

    fn store_if_space<const N: usize>(&mut self, value: T) -> Result<(), F::Error> {
        todo!()
    }
}

impl<'d, F: embedded_storage::nor_flash::NorFlash, T: serde::Deserialize<'d>> NvmLog<F, T> {
    fn read<const N: usize>(&self, buf: &mut u8) -> Result<(), F::Error> {
        todo!()
    }

    fn read_and_erase<const N: usize>(&mut self, buf: &mut u8) -> Result<(), F::Error> {
        todo!()
    }
}
