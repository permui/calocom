use libc::{c_void, memcmp};

use super::length;
use super::{_String, extract_cstr};

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "__calocom_runtime_compare_string"]
pub unsafe extern "C" fn compare_str(s1: *const _String, s2: *const _String) -> i32 {
    let len = length(s1);
    if len != length(s2) {
        -1
    } else {
        memcmp(
            extract_cstr(s1) as *const c_void,
            extract_cstr(s2) as *const c_void,
            len,
        )
    }
}
