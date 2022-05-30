use super::_Float64;
use super::_ObjectType;
use crate::alloc::alloc;

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_f64"]
pub extern "C" fn alloc_f64() -> *mut _Float64 {
    let mem = alloc(::core::mem::size_of::<_Float64>()) as *mut _Float64;
    unsafe {
        (*mem).header.tag = _ObjectType::Float64;
    }
    mem
}

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_f64_literal"]
pub extern "C" fn alloc_f64_literal(i: f64) -> *mut _Float64 {
    let mem = alloc_f64();
    unsafe {
        (*mem).data = i;
    }
    mem
}

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_f64"]
pub unsafe extern "C" fn extract_f64(obj: *const _Float64, _dummy: f64) -> f64 {
    (*obj).data
}
