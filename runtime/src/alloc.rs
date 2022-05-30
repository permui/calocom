use libc::{c_void, calloc, size_t};

use super::panic::panic;
use super::types::*;

#[no_mangle]
#[export_name = "__calocom_runtime_alloc"]
pub extern "C" fn alloc(size: size_t) -> *mut c_void {
    unsafe {
        let ptr = calloc(1, size);
        if ptr.is_null() {
            panic((const_cstr!("allocator returns a null pointer")).as_ptr());
        }
        ptr
    }
}

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_object"]
pub extern "C" fn alloc_object() -> *mut _Object {
    alloc(::core::mem::size_of::<_Object>()) as *mut _Object
}

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_unit"]
pub extern "C" fn alloc_unit() -> *mut _Unit {
    let mem = alloc(::core::mem::size_of::<_Unit>()) as *mut _Unit;
    // TODO: regard keeping a global singleton
    unsafe {
        (*mem).header.tag = _ObjectType::Unit;
        (*mem).header.ptr = 0;
    }
    mem
}
