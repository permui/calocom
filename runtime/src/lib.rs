#![no_std]
#![feature(lang_items)]

pub mod core;
pub mod std;

use libc::exit;

#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[panic_handler]
fn panic(_panic: &::core::panic::PanicInfo<'_>) -> ! {
    unsafe { exit(1) }
}
