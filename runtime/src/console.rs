use crate::panic::panic;
use crate::types::*;

use core::ptr::addr_of;
use libc::c_char;
use libc::c_int;
use libc::printf;
use libc::putchar;

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
pub unsafe fn print_object(p: *const _Object) {
    match (*p).tag {
        _ObjectType::Unit => {
            printf(const_cstr!("()").as_ptr());
        }
        _ObjectType::Str => {
            let s = p as *const _String;
            printf(
                const_cstr!("%.*s").as_ptr(),
                (*s).len,
                addr_of!((*s).data) as *const c_char,
            );
        }
        _ObjectType::Int32 => {
            let i = p as *const _Int32;
            printf(const_cstr!("%d").as_ptr(), (*i).data);
        }
        _ObjectType::Bool => {
            let i = p as *const _Int32;
            printf(if (*i).data != 0 {
                const_cstr!("true").as_ptr()
            } else {
                const_cstr!("false").as_ptr()
            });
        }
        _ObjectType::Reserved => {
            printf(const_cstr!("<reserved>").as_ptr());
        }
        _ObjectType::Float64 => {
            let f = p as *const _Float64;
            printf(const_cstr!("%f").as_ptr(), (*f).data);
        }
        _ObjectType::Tuple => {
            let t = p as *const _Tuple;
            let len = (*t).length as usize;
            printf(const_cstr!("(").as_ptr());
            for i in 0..len {
                if i != 0 {
                    putchar(',' as c_int);
                    putchar(' ' as c_int);
                }
                print_object(
                    (addr_of!((*t).data) as *const *const _Object)
                        .add(len)
                        .read(),
                );
            }
            printf(const_cstr!(")").as_ptr());
        }
        _ObjectType::Enum => {
            printf(const_cstr!("<enum>").as_ptr());
        }
        _ObjectType::Closure => {
            printf(const_cstr!("<closure>").as_ptr());
        }
        _ObjectType::Other => {
            panic(const_cstr!("not supported type: other").as_ptr());
        }
        _ObjectType::Array => {
            let a = p as *const _Array;
            let len = (*a).length as usize;
            printf(const_cstr!("[").as_ptr());
            for i in 0..len {
                if i != 0 {
                    putchar(',' as c_int);
                    putchar(' ' as c_int);
                }
                print_object(((*a).data as *const *const _Object).add(len).read());
            }
            printf(const_cstr!(")").as_ptr());
        }
    }
}
