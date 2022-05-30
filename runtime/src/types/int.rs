use super::_Int32;
use super::_ObjectType;
use crate::alloc::alloc;

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_i32"]
pub extern "C" fn alloc_i32() -> *mut _Int32 {
    let mem = alloc(::core::mem::size_of::<_Int32>()) as *mut _Int32;
    unsafe {
        (*mem).header.tag = _ObjectType::Int32;
    }
    mem
}

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_i32_literal"]
pub extern "C" fn alloc_i32_literal(i: i32) -> *mut _Int32 {
    let mem = alloc_i32();
    unsafe {
        (*mem).data = i;
    }
    mem
}

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_i32"]
pub unsafe extern "C" fn extract_i32(obj: *const _Int32, _dummy: i32) -> i32 {
    (*obj).data
}
