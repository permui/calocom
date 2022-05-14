use crate::panic::panic;
use crate::types::*;
use core::ptr::addr_of;
use libc::c_char;
use libc::printf;
use libc::puts;

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
pub unsafe fn print_object(p: *const _Object) {
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
            puts(if (*i).data != 0 {
                true_s.as_ptr()
            } else {
                false_s.as_ptr()
            });
        }
        _ => {
            let msg = const_cstr!("not supported type");
            panic(msg.as_ptr());
        }
    }
}
