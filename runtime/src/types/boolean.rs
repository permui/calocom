use super::_Int32;
use super::_ObjectType;

use crate::alloc::alloc;
use crate::panic::panic;

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_bool"]
pub extern "C" fn alloc_bool() -> *mut _Int32 {
    let mem = alloc(::core::mem::size_of::<_Int32>()) as *mut _Int32;
    unsafe {
        (*mem).header.tag = _ObjectType::Bool;
    }
    mem
}

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_bool_literal"]
pub extern "C" fn alloc_bool_literal(i: bool) -> *mut _Int32 {
    let mem = alloc_bool();
    unsafe {
        (*mem).data = i as i32;
    }
    mem
}

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_bool"]
pub unsafe extern "C" fn extract_bool(obj: *const _Int32, _dummy: bool) -> i32 {
    let b = (*obj).data;
    if b == 0 || b == 1   {
        b
    } else {
        panic(const_cstr!("not valid boolean value").as_ptr());
    }
}
