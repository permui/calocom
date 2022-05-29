use crate::types::*;
use libc::c_char;
use libc::exit;
use libc::printf;

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_dummy"]
#[no_mangle]
pub unsafe extern "C" fn dummy(
    _o: *mut _Object,
    _s: *mut _String,
    _i: *mut _Int32,
    _t: *mut _Tuple,
) -> ! {
    panic(const_cstr!("this function should not be used").as_ptr())
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_entry_panic_block"]
pub unsafe extern "C" fn entry_panic_block() -> ! {
    panic(const_cstr!("panic: entry the panic basic block").as_ptr())
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_panic"]
pub unsafe extern "C" fn panic(msg: *const c_char) -> ! {
    printf(const_cstr!("calocom runtime panic: %s\n").as_ptr(), msg);
    exit(1)
}
