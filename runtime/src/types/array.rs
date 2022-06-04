use super::_Array;
use super::_Int32;
use super::_Object;
use super::_ObjectType;
use super::extract_i32;
use crate::alloc::alloc;
use crate::alloc::dealloc;
use crate::panic::panic;

use libc::c_void;
use libc::memcpy;
use libc::printf;
use libc::size_t;

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_array"]
pub extern "C" fn alloc_array(capacity: size_t) -> *mut _Array {
    unsafe {
        let capacity = ::core::cmp::max(capacity, 4);
        let mem = alloc(::core::mem::size_of::<_Array>()) as *mut _Array;
        (*mem).header.tag = _ObjectType::Array;
        (*mem).length = 0;
        (*mem).capacity = capacity as u32;
        (*mem).data =
            alloc(capacity * ::core::mem::size_of::<*mut _Object>()) as *mut [*mut _Object; 0];
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
        printf(
            const_cstr!("try access [%d] but limit is [%d]\n").as_ptr(),
            subscript,
            (*array).length,
        );
        panic(const_cstr!("array bound checking failed").as_ptr());
    }
    ((*array).data as *mut *mut _Object).add(subscript as usize)
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_get_array_length"]
pub unsafe extern "C" fn get_array_length(array: *const _Array) -> usize {
    (*array).length as usize
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_array_grow"]
pub unsafe extern "C" fn array_grow(array: *mut _Array) {
    let old_capacity = (*array).capacity as usize;
    let new_capacity = ::core::cmp::max(4, old_capacity + old_capacity / 2);

    let new_data = alloc(new_capacity * ::core::mem::size_of::<*mut _Object>());
    memcpy(
        new_data,
        (*array).data as *const c_void,
        (*array).length as usize * ::core::mem::size_of::<*mut _Object>(),
    );
    dealloc((*array).data as *mut c_void);
    (*array).data = new_data as *mut [*mut _Object; 0];
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_array_copy"]
pub unsafe extern "C" fn array_copy(target: *mut _Array, source: *mut _Array) {
    let len = ::core::cmp::min((*target).length, (*source).length);
    memcpy(
        (*target).data as *mut c_void,
        (*source).data as *mut c_void,
        len as usize * ::core::mem::size_of::<*mut _Object>(),
    );
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_array_push_back"]
pub unsafe extern "C" fn array_push_back(array: *mut _Array, elem: *mut _Object) {
    if (*array).length == (*array).capacity {
        array_grow(array);
    }
    let length = (*array).length;
    ((*array).data as *mut *mut _Object)
        .add(length as usize)
        .write(elem);
    (*array).length += 1;
}
