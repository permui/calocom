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
pub unsafe extern "C" fn compare_str(s1: *const _String, s2: *const _String) -> i32 {
    let len = get_string_length(s1);
    if len != get_string_length(s2) {
        -1
    } else {
        memcmp(
            extract_cstr(s1) as *const c_void,
            extract_cstr(s2) as *const c_void,
            len,
        )
    }
}
