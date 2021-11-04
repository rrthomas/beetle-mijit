use libc::{c_char, c_int};
use std::{ptr}; 
use std::ffi::{CStr, CString};

pub mod vm;
pub use vm::{VM, Registers, BeetleExit, DATA_CELLS, RETURN_CELLS, CELL};

unsafe fn char_array_to_string(array: *const c_char) -> CString {
    CStr::from_ptr(array).to_owned()
}

unsafe fn char_array_array_to_vec(array: *const *const c_char) -> Vec<CString> {
    let mut result = Vec::new();
    loop {
        let data = ptr::read(array.offset(result.len() as isize));
        if data.is_null() {
            return result;
        }
        result.push(char_array_to_string(data));
    }
}

/** Allocates a new VM. */
#[no_mangle]
pub unsafe extern fn mijit_beetle_new(
    argv: *const *const c_char,
    memory_cells: u32,
    data_cells: u32,
    return_cells: u32,
) -> Box<VM> {
    Box::new(VM::new(
        char_array_array_to_vec(argv).into(),
        memory_cells,
        data_cells,
        return_cells,
    ))
}


/** Frees a Buffer. */
#[no_mangle]
pub extern fn mijit_beetle_drop(_vm: Box<VM>) {}

/** Read or write the public registers. */
#[no_mangle]
pub extern fn mijit_beetle_registers_mut(vm: &mut VM) -> &mut Registers { vm.registers_mut() }

/**
 * Run the code at address `ep`.
 */
#[no_mangle]
pub unsafe extern fn mijit_beetle_run(vm: &mut VM, ep: u32) -> c_int {
    use BeetleExit::*;
    match vm.run(ep) {
        Halt(reason) => reason as c_int,
        NotImplemented(_) => -256,
        Undefined(_) => -256,
        InvalidLibRoutine(_) => -257,
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
}
