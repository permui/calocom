use crate::types::*;
use libc::c_char;
use libc::exit;
use libc::printf;

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
pub unsafe extern "C" fn __calocom_runtime_dummy(
    _o: *mut _Object,
    _s: *mut _String,
    _i: *mut _Int32,
    _t: *mut _Tuple,
) -> ! {
    let fmt = const_cstr!("this function should not be used");
    __calocom_runtime_panic(fmt.as_ptr())
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
pub unsafe extern "C" fn __calocom_runtime_entry_panic_block() -> ! {
    let fmt = const_cstr!("panic: entry the panic basic block");
    __calocom_runtime_panic(fmt.as_ptr())
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
pub unsafe extern "C" fn __calocom_runtime_panic(msg: *const c_char) -> ! {
    let fmt = const_cstr!("calocom runtime panic: %s\n");
    printf(fmt.as_ptr(), msg);
    exit(1)
}