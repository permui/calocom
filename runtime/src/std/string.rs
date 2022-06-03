use libc::strpbrk;

use crate::types::_Object;
use crate::types::alloc_array;
use crate::types::alloc_string_literal;
use crate::types::array_push_back;
use crate::types::extract_cstr;
use crate::types::_String;
use crate::types::_Array;
use crate::types::get_string_length;

/// # Safety
///
/// This function should not be called directly by other crates
#[no_mangle]
#[export_name = "_CALOCOM_PF_3std6string5splitfCaCsCsCs"]
pub unsafe extern "C" fn split(s: *const _String, delim: *const _String) -> *const _Array {
    let cs = extract_cstr(s);
    let len = get_string_length(s);
    let delim = extract_cstr(delim);

    let arr = alloc_array(4);
    let mut p = cs;

    loop {
        let c = p;
        p = strpbrk(p, delim);
        
        if p.is_null() {
            let last_len = len - (c.offset_from(cs) as usize);
            let str = alloc_string_literal(last_len, c);
            array_push_back(arr, str as *mut _Object);
            break;
        } else {
            let seg_len = p.offset_from(c) as usize;
            let str = alloc_string_literal(seg_len, c);
            array_push_back(arr, str as *mut _Object);
            p = p.add(1);
        }
    }

    arr
}