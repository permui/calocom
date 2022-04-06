use crate::core::*;
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
/// Parameter 0: P0_ o: Calocom.object
/// Return Type: RT Calocom.unit
#[no_mangle]
pub unsafe extern "C" fn _CM3stdM2ioPF5printP0_1oCoRTCu(p: *const _Object) -> *const _Object {
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
/// Parameter 0: P0_ o: Calocom.object
/// Return Type: RT Calocom.unit
#[no_mangle]
pub unsafe extern "C" fn _CM3stdM2ioPF7printlnP0_1oCoRTCu(p: *const _Object) -> *const _Object {
    __calocom_runtime_print_object(p);
    #[cfg(windows)]
    putchar('\r' as c_int);
    putchar('\n' as c_int);
    __calocom_runtime_alloc_unit()
}
