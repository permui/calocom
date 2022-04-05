use libc::c_char;
use libc::c_uint;
use libc::c_void;
use libc::size_t;
use libc::calloc;
use libc::exit;
use libc::memcpy;
use libc::printf;

#[repr(C)]
pub struct _String {
    pub len: c_uint,
    pub data: c_char,
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
pub unsafe extern "C" fn __calocom_panic(msg: *const i8) -> ! {
    printf("calocom runtime panic: %s\n\0".as_ptr() as *const i8, msg);
    exit(1)
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_object(size: size_t) -> *mut c_void {
    unsafe { calloc(1, size) }
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_string(length: size_t) -> *mut _String {
    unsafe {
        if length > c_uint::MAX as size_t {
            __calocom_panic("string length exceeded\0".as_ptr() as *const i8);
        };
        // length size + string size + trailing zero size
        let mem = __calocom_runtime_alloc_object(length + ::core::mem::size_of::<_String>()) as *mut _String;
        (*mem).len = length as c_uint;
        mem
    }
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_string_literal(length: size_t, s: *const i8) {
    let buf = __calocom_runtime_alloc_string(length);
    unsafe {
        memcpy((*buf).data as *mut c_void, s as *const c_void, length);
    }
}
