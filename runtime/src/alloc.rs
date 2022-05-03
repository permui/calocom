use core::ptr::addr_of_mut;

use libc::{c_char, c_void, calloc, memcpy, size_t};

use super::panic::__calocom_runtime_panic;
use super::types::*;

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc(size: size_t) -> *mut c_void {
    unsafe {
        let ptr = calloc(1, size);
        if ptr.is_null() {
            let fmt = const_cstr!("allocation returns a null pointer");
            __calocom_runtime_panic(fmt.as_ptr());
        }
        ptr
    }
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_object() -> *mut _Object {
    __calocom_runtime_alloc(::core::mem::size_of::<_Object>()) as *mut _Object
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_unit() -> *mut _Unit {
    let mem = __calocom_runtime_alloc(::core::mem::size_of::<_Unit>()) as *mut _Unit;
    // TODO: regard keeping a global singleton
    unsafe {
        (*mem).header.tag = _ObjectType::Unit;
        (*mem).header.ptr = 0;
    }
    mem
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_string(length: size_t) -> *mut _String {
    unsafe {
        if length > u32::MAX as size_t {
            let fmt = const_cstr!("string length exceeded");
            __calocom_runtime_panic(fmt.as_ptr());
        };
        // length size + string length + trailing zero size
        let mem =
            __calocom_runtime_alloc(length + 1 + ::core::mem::size_of::<_String>()) as *mut _String;
        (*mem).header.tag = _ObjectType::Str;
        (*mem).len = length as u32;
        mem
    }
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_string_literal(
    length: size_t,
    s: *const c_char,
) -> *mut _String {
    let buf = __calocom_runtime_alloc_string(length);
    unsafe {
        memcpy(
            addr_of_mut!((*buf).data) as *mut c_void,
            s as *const c_void,
            length,
        );
    }
    buf
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_i32() -> *mut _Int32 {
    let mem = __calocom_runtime_alloc(::core::mem::size_of::<_Int32>()) as *mut _Int32;
    unsafe {
        (*mem).header.tag = _ObjectType::I32;
    }
    mem
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_i32_literal(i: i32) -> *mut _Int32 {
    let mem = __calocom_runtime_alloc_i32();
    unsafe {
        (*mem).data = i;
    }
    mem
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_bool() -> *mut _Int32 {
    let mem = __calocom_runtime_alloc(::core::mem::size_of::<_Int32>()) as *mut _Int32;
    unsafe {
        (*mem).header.tag = _ObjectType::Bool;
    }
    mem
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_bool_literal(i: bool) -> *mut _Int32 {
    let mem = __calocom_runtime_alloc_bool();
    unsafe {
        (*mem).data = i as i32;
    }
    mem
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_tuple(n: size_t) -> *mut _Tuple {
    let mem = __calocom_runtime_alloc(
        ::core::mem::size_of::<_Tuple>() + n * ::core::mem::size_of::<*mut c_void>(),
    ) as *mut _Tuple;
    unsafe {
        (*mem).header.tag = _ObjectType::Tuple;
    }
    mem
}
