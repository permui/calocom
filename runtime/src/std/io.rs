use crate::alloc::alloc_unit;
use crate::console::print_object;
use crate::panic::panic;
use crate::types::*;

use libc::c_char;
use libc::c_int;
use libc::getchar;
use libc::printf;
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

/// # Safety
///
/// This function should not be called directly by other crates
///
#[no_mangle]
#[export_name = "_CALOCOM_PF_3std2io20print_i32_with_alignfCuCi4CsCi4"]
pub unsafe extern "C" fn print_i32_with_align(
    i: *const _Int32,
    dir: *const _String,
    width: *const _Int32,
) -> *const _Unit {
    let left_align = const_cstr!("<");
    let right_align = const_cstr!(">");
    let width = extract_i32(width, 0);
    let value = extract_i32(i, 0);

    if compare_str_with_cstr(dir, left_align.as_ptr(), left_align.len() as u32) == 0 {
        printf(const_cstr!("%-*d").as_ptr(), width, value);
    } else if compare_str_with_cstr(dir, right_align.as_ptr(), right_align.len() as u32) == 0 {
        printf(const_cstr!("%*d").as_ptr(), width, value);
    } else {
        panic(const_cstr!("not available align specifier").as_ptr());
    }

    alloc_unit()
}

#[no_mangle]
#[export_name = "_CALOCOM_PF_3std2io8read_i32fCi4"]
pub extern "C" fn read_i32() -> *const _Int32 {
    let mut n = 0;
    unsafe {
        scanf(const_cstr!("%d").as_ptr(), &mut n as *mut i32);
    }
    alloc_i32_literal(n)
}

#[no_mangle]
#[export_name = "_CALOCOM_PF_3std2io8read_f64fCf8"]
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
