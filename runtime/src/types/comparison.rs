use libc::c_char;
use libc::c_void;
use libc::memcmp;

use super::_String;
use super::extract_cstr;
use super::get_string_length;

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_compare_string"]
pub unsafe extern "C" fn compare_str(s1: *const _String, s2: *const _String, eq: bool) -> bool {
    let len = get_string_length(s1);
    if len != get_string_length(s2) {
        !eq
    } else {
        let no_diff = memcmp(
            extract_cstr(s1) as *const c_void,
            extract_cstr(s2) as *const c_void,
            len,
        ) == 0;
        if eq {
            no_diff
        } else {
            !no_diff
        }
    }
}

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_compare_string_with_cstr"]
pub unsafe extern "C" fn compare_str_with_cstr(
    s1: *const _String,
    s2: *const c_char,
    length: u32,
) -> i32 {
    if get_string_length(s1) != length {
        -1
    } else {
        (memcmp(
            extract_cstr(s1) as *const c_void,
            s2 as *const c_void,
            length,
        ) != 0) as i32
    }
}
