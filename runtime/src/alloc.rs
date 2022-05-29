use core::ptr::addr_of_mut;

use libc::{c_char, c_void, calloc, memcpy, size_t};

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

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_string"]
pub extern "C" fn alloc_string(length: size_t) -> *mut _String {
    unsafe {
        if length > u32::MAX as size_t {
            panic(const_cstr!("string length exceeded").as_ptr());
        };
        // length size + string length + trailing zero size
        let mem = alloc(length + 1 + ::core::mem::size_of::<_String>()) as *mut _String;
        (*mem).header.tag = _ObjectType::Str;
        (*mem).len = length as u32;
        mem
    }
}

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_string_literal"]
pub extern "C" fn alloc_string_literal(length: size_t, s: *const c_char) -> *mut _String {
    let buf = alloc_string(length);
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

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_tuple"]
pub extern "C" fn alloc_tuple(n: size_t) -> *mut _Tuple {
    let mem = alloc(::core::mem::size_of::<_Tuple>() + n * ::core::mem::size_of::<*mut c_void>())
        as *mut _Tuple;
    unsafe {
        if n > 8 as size_t {
            panic(const_cstr!("the number of tuple fields exceeded 8").as_ptr());
        }
        (*mem).header.tag = _ObjectType::Tuple;
        (*mem).header.reserved1 = n as u8;
    }
    mem
}

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_enum"]
pub extern "C" fn alloc_enum() -> *mut _Enum {
    let mem = alloc(::core::mem::size_of::<_Enum>()) as *mut _Enum;
    unsafe {
        (*mem).header.tag = _ObjectType::Enum;
    }
    mem
}
