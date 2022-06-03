use core::ptr::addr_of;

use crate::panic::panic;
use crate::types::_Array;
use crate::types::_Closure;
use crate::types::_Int32;
use crate::types::_Object;
use crate::types::_ObjectType;
use crate::types::alloc_array;
use crate::types::alloc_i32_literal;
use crate::types::array_push_back;
use crate::types::extract_i32;

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "_CALOCOM_PF_3std5array3newfCaCoCi4Co"]
pub unsafe extern "C" fn new(length: *const _Int32, initializer: *const _Object) -> *const _Array {
    type InitializerType = unsafe extern "C" fn(*const _Object, *const _Int32) -> *mut _Object;
    if !matches!((*initializer).tag, _ObjectType::Closure) {
        panic(const_cstr!("the initializer of a array must be a callable closure with type (_: i32) -> object").as_ptr());
    }
    let closure = initializer as *const _Closure;
    let fn_ptr_addr = (addr_of!((*closure).fn_ptr) as *mut *const ()).read();
    let fn_ptr = ::core::mem::transmute::<*const (), InitializerType>(fn_ptr_addr);
    let len = extract_i32(length, 0);
    let arr = alloc_array(len as usize);
    for i in 0..len {
        let index = alloc_i32_literal(i as i32);
        let element = fn_ptr(initializer, index);
        array_push_back(arr, element);
    }
    arr
}
