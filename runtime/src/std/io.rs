use crate::alloc::alloc_unit;
use crate::console::print_object;
use crate::types::*;
use libc::c_int;
use libc::putchar;

/// # Safety
///
/// This function should not be called directly by other crates
///
#[no_mangle]
#[export_name = "TODO1"]
pub unsafe extern "C" fn print(p: *const _Object) -> *const _Unit {
    print_object(p);
    alloc_unit()
}

/// # Safety
///
/// This function should not be called directly by other crates
///
#[no_mangle]
#[export_name = "TODO2"]
pub unsafe extern "C" fn println(p: *const _Object) -> *const _Unit {
    print_object(p);
    #[cfg(windows)]
    putchar('\r' as c_int);
    putchar('\n' as c_int);
    alloc_unit()
}
