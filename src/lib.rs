use libc::{c_int};

pub mod vm;
pub use vm::{VM, Registers, BeetleExit, DATA_CELLS, RETURN_CELLS, CELL};

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
        Lib => -257,
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
}
