use libc::c_char;
use libc::c_void;
use libc::calloc;
use libc::exit;
use libc::memcpy;
use libc::printf;
use libc::puts;
use libc::size_t;
use libc::uintptr_t;

#[repr(C)]
pub enum _ObjectType {
    Unit = 0,
    Str = 1,
    I32 = 2,
    Bool = 3,
    Other = 4,
}

#[repr(C)]
pub struct _Object {
    pub tag: _ObjectType,
    pub ptr: uintptr_t,
}

#[repr(C)]
pub struct _String {
    pub header: _Object,
    pub len: u32,
    pub data: c_char,
}

#[repr(C)]
pub struct _I32 {
    pub header: _Object,
    pub data: i32,
}
/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
pub unsafe extern "C" fn __calocom_panic(msg: *const c_char) -> ! {
    let fmt = const_cstr!("calocom runtime panic: %s\n");
    printf(fmt.as_ptr(), msg);
    exit(1)
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_object(size: size_t) -> *mut c_void {
    unsafe { calloc(1, size) }
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_unit() -> *mut _Object {
    let obj = __calocom_runtime_alloc_object(::core::mem::size_of::<_Object>()) as *mut _Object;
    // TODO: regard keep a global singleton
    unsafe {
        (*obj).tag = _ObjectType::Unit;
        (*obj).ptr = 0;
    }
    obj
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_string(length: size_t) -> *mut _String {
    unsafe {
        if length > u32::MAX as size_t {
            let fmt = const_cstr!("string length exceeded");
            __calocom_panic(fmt.as_ptr());
        };
        // length size + string length + trailing zero size
        let mem = __calocom_runtime_alloc_object(length + ::core::mem::size_of::<_String>())
            as *mut _String;
        (*mem).header.tag = _ObjectType::Str;
        (*mem).len = length as u32;
        mem
    }
}

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_string_literal(length: size_t, s: *const c_char) {
    let buf = __calocom_runtime_alloc_string(length);
    unsafe {
        memcpy((*buf).data as *mut c_void, s as *const c_void, length);
    }
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
            printf(fmt.as_ptr(), (*s).len, &(*s).data as *const c_char);
        }
        _ObjectType::I32 => {
            let i = p as *const _I32;
            let fmt = const_cstr!("%d");
            printf(fmt.as_ptr(), (*i).data);
        }
        _ObjectType::Bool => {
            let i = p as *const _I32;
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
            __calocom_panic(msg.as_ptr());
        }
    }
}
