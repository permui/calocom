use crate::alloc::alloc_unit;
use crate::console::print_object;
use crate::types::*;

use libc::c_char;
use libc::c_int;
use libc::getchar;
use libc::putchar;
use libc::scanf;

/// # Safety
///
/// This function should not be called directly by other crates
///
#[no_mangle]
#[export_name = "_CALOCOM_PF_3std2io5printfCuCo"]
pub unsafe extern "C" fn print(p: *const _Object) -> *const _Unit {
    print_object(p);
    alloc_unit()
}

/// # Safety
///
/// This function should not be called directly by other crates
///
#[no_mangle]
#[export_name = "_CALOCOM_PF_3std2io7printlnfCuCo"]
pub unsafe extern "C" fn println(p: *const _Object) -> *const _Unit {
    print_object(p);
    #[cfg(windows)]
    putchar('\r' as c_int);
    putchar('\n' as c_int);
    alloc_unit()
}

#[no_mangle]
#[export_name = "TODO4"]
pub extern "C" fn read_i32() -> *const _Int32 {
    let mut n = 0;
    unsafe {
        scanf(const_cstr!("%d").as_ptr(), &mut n as *mut i32);
    }
    alloc_i32_literal(n)
}

#[no_mangle]
#[export_name = "TODO5"]
pub extern "C" fn read_f64() -> *const _Float64 {
    let mut n = 0.;
    unsafe {
        scanf(const_cstr!("%lf").as_ptr(), &mut n as *mut f64);
    }
    alloc_f64_literal(n)
}

#[no_mangle]
#[export_name = "_CALOCOM_PF_3std2io6readlnfCs"]
pub extern "C" fn readln() -> *const _String {
    const BUF_SIZE: usize = 16;
    let mut buffer: [c_char; BUF_SIZE] = Default::default();
    let mut str: Option<*mut _String> = None;

    loop {
        let mut count = 0;
        let mut reached_end = false;
        #[allow(clippy::needless_range_loop)]
        for i in 0..BUF_SIZE {
            let ch = unsafe { getchar() };
            if ch == -1 || ch == b'\n' as i32 {
                reached_end = true;
                break;
            }
            buffer[i] = ch as c_char;
            count += 1;
        }
        if let Some(s) = str {
            str = Some(unsafe { append_buffer(s as *const _String, buffer.as_ptr(), count) });
        } else {
            str = Some(alloc_string_literal(count, buffer.as_ptr()));
        }
        if reached_end {
            break;
        }
    }
    unsafe { str.unwrap_unchecked() }
}
