use super::_Array;
use super::_Int32;
use super::_Object;
use super::_ObjectType;
use super::extract_i32;
use crate::alloc::alloc;
use crate::panic::panic;

use libc::size_t;

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_array"]
pub extern "C" fn alloc_array(length: size_t) -> *mut _Array {
    unsafe {
        let cap = length.next_power_of_two();
        let mem = alloc(::core::mem::size_of::<_Array>()) as *mut _Array;
        (*mem).header.tag = _ObjectType::Array;
        (*mem).length = length as u32;
        (*mem).capacity = cap as u32;
        (*mem).data = alloc(cap * ::core::mem::size_of::<*mut _Object>()) as *mut [*mut _Object; 0];
        mem
    }
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_array_index"]
pub unsafe extern "C" fn array_index(
    array: *mut _Array,
    index: *const _Int32,
) -> *mut *mut _Object {
    let subscript = extract_i32(index, 0);
    if subscript < 0 || subscript as u32 >= (*array).length {
        panic(const_cstr!("array bound checking failed").as_ptr());
    }
    ((*array).data as *mut *mut _Object).add(subscript as usize)
}
