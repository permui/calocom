#![no_std]
#![feature(lang_items)]

pub mod core;
pub mod std;

#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[panic_handler]
fn panic(_panic: &::core::panic::PanicInfo<'_>) -> ! {
    unsafe {
        core::__calocom_panic("\0".as_ptr() as *const i8)
    }
}
