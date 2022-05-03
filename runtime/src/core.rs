use core::ptr::addr_of;
use core::ptr::addr_of_mut;

use libc::c_char;
use libc::c_void;
use libc::calloc;
use libc::exit;
use libc::memcpy;
use libc::printf;
use libc::puts;
use libc::size_t;
use libc::uintptr_t;

#[repr(u8)]
pub enum _ObjectType {
    Reserved = 0,
    Unit = 1,
    Str = 2,
    I32 = 3,
    Bool = 4,
    Other = 5,
}

#[repr(C, packed(4))]
pub struct _Object {
    pub ptr: uintptr_t,
    pub tag: _ObjectType,
    pub reserved1: u8,
    pub reserved2: u16,
}

#[repr(C, packed)]
pub struct _String {
    pub header: _Object,
    pub len: u32,
    pub data: [c_char; 0],
}

#[repr(C, packed)]
pub struct _Int32 {
    pub header: _Object,
    pub data: i32,
}

#[repr(C, packed)]
pub struct _Tuple {
    pub header: _Object,
    pub data: [*mut c_void; 0],
}

#[repr(C, packed)]
pub struct _Unit {
    pub header: _Object,
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
pub unsafe extern "C" fn __calocom_runtime_dummy(
    _o: *mut _Object,
    _s: *mut _String,
    _i: *mut _Int32,
    _t: *mut _Tuple,
) -> ! {
    let fmt = const_cstr!("this function should not be used");
    __calocom_runtime_panic(fmt.as_ptr())
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
pub unsafe extern "C" fn __calocom_runtime_panic(msg: *const c_char) -> ! {
    let fmt = const_cstr!("calocom runtime panic: %s\n");
    printf(fmt.as_ptr(), msg);
    exit(1)
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc(size: size_t) -> *mut c_void {
    unsafe { calloc(1, size) }
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

/// # Safety
///
/// This function should not be called directly by other crates
pub unsafe fn __calocom_runtime_print_object(p: *const _Object) {
    match (*p).tag {
        _ObjectType::Unit => {
            let fmt = const_cstr!("()");
            puts(fmt.as_ptr());
        }
        _ObjectType::Str => {
            let s = p as *const _String;
            let fmt = const_cstr!("%.*s");
            printf(fmt.as_ptr(), (*s).len, addr_of!((*s).data) as *const c_char);
        }
        _ObjectType::I32 => {
            let i = p as *const _Int32;
            let fmt = const_cstr!("%d");
            printf(fmt.as_ptr(), (*i).data);
        }
        _ObjectType::Bool => {
            let i = p as *const _Int32;
            let true_s = const_cstr!("true");
            let false_s = const_cstr!("false");
            puts(if (*i).data == 0 {
                true_s.as_ptr()
            } else {
                false_s.as_ptr()
            });
        }
        _ => {
            let msg = const_cstr!("not supported type");
            __calocom_runtime_panic(msg.as_ptr());
        }
    }
}
