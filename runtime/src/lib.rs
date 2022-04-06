#![no_std]
#![feature(lang_items)]

#[macro_use]
pub mod aux;
pub mod core;
pub mod std;

#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[panic_handler]
fn panic(_panic: &::core::panic::PanicInfo<'_>) -> ! {
    unsafe {
        let fmt = const_cstr!("");
        core::__calocom_panic(fmt.as_ptr())
    }
}
