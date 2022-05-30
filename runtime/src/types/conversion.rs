use super::_Float64;
use super::_Int32;
use super::alloc_f64_literal;
use super::alloc_i32_literal;
use super::extract_f64;
use super::extract_i32;

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_i32_to_f64"]
pub unsafe extern "C" fn i32_to_f64(i: *const _Int32) -> *mut _Float64 {
    let i = extract_i32(i, 0);
    alloc_f64_literal(i as f64)
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_f64_to_i32"]
pub unsafe extern "C" fn f64_to_i32(f: *const _Float64) -> *mut _Int32 {
    let f = extract_f64(f, 0.);
    alloc_i32_literal(f as i32)
}
