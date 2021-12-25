use libc::{c_int};

mod machine;
use machine::{CELL, Machine, State, Trap};

pub mod vm;
use vm::{VM, Registers, BeetleExit};

/** Allocates a new VM. */
#[no_mangle]
pub unsafe extern fn mijit_beetle_new(
    memory_cells: u32,
    data_cells: u32,
    return_cells: u32,
) -> Box<VM> {
    Box::new(VM::new(
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

/** Read M0. */
#[no_mangle]
pub extern fn mijit_beetle_M0(vm: &VM) -> *const u32 { vm.memory().as_ptr() }

/**
 * Run the code at address `ep`.
 */
#[no_mangle]
pub unsafe extern fn mijit_beetle_run(vm: &mut VM, ep: u32) -> c_int {
    use BeetleExit::*;
    match vm.run(ep) {
        Halt(reason) => reason as c_int,
        NotImplemented => -511,
        Undefined(_) => -256,
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
}
