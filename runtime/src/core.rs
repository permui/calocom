use libc::c_void;
use libc::calloc;

#[no_mangle]
pub extern "C" fn __calocom_runtime_alloc_object(size: u32) -> *mut c_void {
    unsafe { calloc(1, size as usize) }
}

