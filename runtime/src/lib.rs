#![no_std]
#![feature(lang_items)]

#[macro_use]
pub mod aux;
pub mod core;
pub mod std;

#[cfg(not(test))]
#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[cfg(not(test))]
#[panic_handler]
fn panic(_panic: &::core::panic::PanicInfo<'_>) -> ! {
    unsafe {
        let fmt = const_cstr!("");
        core::__calocom_runtime_panic(fmt.as_ptr())
    }
}
