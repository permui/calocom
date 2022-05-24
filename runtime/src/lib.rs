#![no_std]
#![feature(lang_items)]

#[macro_use]
mod aux;
pub mod alloc;
pub mod console;
pub mod panic;
pub mod std;
pub mod types;

#[cfg(not(test))]
#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[cfg(not(test))]
#[panic_handler]
fn panic(_panic: &::core::panic::PanicInfo<'_>) -> ! {
    unsafe {
        let fmt = const_cstr!("");
        panic::panic(fmt.as_ptr())
    }
}

extern "C" {
    #[link_name = "_CPF4mainRTCu"]
    fn user_main() -> *mut types::_Unit;
}

#[no_mangle]
#[export_name = "main"]
pub extern "C" fn runtime_main(_argc: i32, _argv: *const *const libc::c_char) -> i32 {
    unsafe {
        user_main();
    }
    0
}
