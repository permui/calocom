use crate::alloc::__calocom_runtime_alloc_unit;
use crate::console::__calocom_runtime_print_object;
use crate::types::*;
use libc::c_int;
use libc::putchar;

/// # Safety
///
/// This function should not be called directly by other crates
///
/// Calocom Library Function: _C
/// Module: M 3 std
/// Module: M 2 io
/// Polymorphic Function: PF 5 print
/// Parameter 0: P0_ Calocom.object
/// Return Type: RT Calocom.unit
#[no_mangle]
pub unsafe extern "C" fn _CM3stdM2ioPF5printP0_CoRTCu(p: *const _Object) -> *const _Unit {
    __calocom_runtime_print_object(p);
    __calocom_runtime_alloc_unit()
}

/// # Safety
///
/// This function should not be called directly by other crates
///
/// Calocom Library Function: _C
/// Module: M 3 std
/// Module: M 2 io
/// Polymorphic Function: PF 7 println
/// Parameter 0: P0_ Calocom.object
/// Return Type: RT Calocom.unit
#[no_mangle]
pub unsafe extern "C" fn _CM3stdM2ioPF7printlnP0_CoRTCu(p: *const _Object) -> *const _Unit {
    __calocom_runtime_print_object(p);
    #[cfg(windows)]
    putchar('\r' as c_int);
    putchar('\n' as c_int);
    __calocom_runtime_alloc_unit()
}
