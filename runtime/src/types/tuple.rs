use super::_Object;
use super::_Tuple;
use crate::alloc::alloc_tuple;
use core::ptr::addr_of_mut;

use paste::paste;

macro_rules! define_tuple_construct_function {
    {$n:literal, $({$i:literal, $param:ident}),+} => {
        paste! {
            /// # Safety
            ///
            /// This function should not be called directly by other crates
            #[export_name = concat!("__calocom_runtime_construct_tuple_", stringify!($n))]
            pub unsafe extern "C" fn [<construct_tuple_ $n>] ($($param: *mut _Object),+) -> *mut _Tuple {
                let p = alloc_tuple($n);
                $((*(addr_of_mut!((*p).data) as *mut *mut _Object).offset($i)) = $param);+;
                p
            }
        }
    };
}

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_tuple_length"]
pub unsafe extern "C" fn extract_tuple_length(t: *mut _Tuple) -> usize {
    (*t).header.reserved1 as usize
}

/// # Safety
///
/// This function should not be called directly by other crates
#[export_name = "__calocom_runtime_extract_tuple_field"]
pub unsafe extern "C" fn extract_tuple_field(t: *mut _Tuple, field_index: i32) -> *mut _Object {
    *(addr_of_mut!((*t).data) as *mut *mut _Object).offset(field_index as isize)
}

define_tuple_construct_function! {1, {0, f0}}
define_tuple_construct_function! {2, {0, f0}, {1, f1}}
define_tuple_construct_function! {3, {0, f0}, {1, f1}, {2, f2}}
define_tuple_construct_function! {4, {0, f0}, {1, f1}, {2, f2}, {3, f3}}
define_tuple_construct_function! {5, {0, f0}, {1, f1}, {2, f2}, {3, f3}, {4, f4}}
define_tuple_construct_function! {6, {0, f0}, {1, f1}, {2, f2}, {3, f3}, {4, f4}, {5, f5}}
define_tuple_construct_function! {7, {0, f0}, {1, f1}, {2, f2}, {3, f3}, {4, f4}, {5, f5}, {6, f6}}
define_tuple_construct_function! {8, {0, f0}, {1, f1}, {2, f2}, {3, f3}, {4, f4}, {5, f5}, {6, f6}, {7, f7}}
