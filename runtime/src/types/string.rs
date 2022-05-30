use super::_ObjectType;
use super::_String;
use crate::alloc::alloc;

use core::ptr::addr_of;
use core::ptr::addr_of_mut;
use libc::c_char;
use libc::c_void;
use libc::memcpy;
use libc::size_t;

#[no_mangle]
#[export_name = "__calocom_runtime_alloc_string"]
pub extern "C" fn alloc_string(length: size_t) -> *mut _String {
    unsafe {
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

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_extract_cstr"]
pub unsafe extern "C" fn extract_cstr(s: *const _String) -> *const c_char {
    addr_of!((*s).data) as *const c_char
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_get_string_length"]
pub unsafe extern "C" fn length(s: *const _String) -> usize {
    (*s).len as usize
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_append_buffer_to_string"]
pub unsafe extern "C" fn append_buffer(
    s: *const _String,
    buffer: *const c_char,
    buffer_length: usize,
) -> *mut _String {
    let old_length = length(s);
    let new_length = old_length + buffer_length;
    let new_str = alloc_string_literal(new_length, extract_cstr(s));
    memcpy(
        (addr_of_mut!((*new_str).data) as *mut c_char).add(old_length) as *mut c_void,
        buffer as *const c_void,
        buffer_length,
    );
    new_str
}
