use libc::{c_int};
use mijit::target::{Native, native, Word};
use mijit::{jit};
use mijit::code::{Global};

mod machine;
use machine::{Registers, CELL, Machine, State, Trap};

/** The state of the JIT compiler. */
pub struct Jit(Option<jit::Jit<Machine, Native>>);

/** Indicate whether an address is cell-aligned. */
fn is_aligned(addr: u32) -> bool {
    addr & 0x3 == 0
}

/** Allocates a new Jit. */
#[no_mangle]
pub extern fn mijit_beetle_new() -> Box<Jit> {
    Box::new(Jit(Some(jit::Jit::new(&Machine, native()))))
}

/** Frees a Jit. */
#[no_mangle]
pub extern fn mijit_beetle_drop(_vm: Box<Jit>) {}

/** Run the code at address `registers.ep`. */
#[no_mangle]
pub unsafe extern fn mijit_beetle_run(
    jit: &mut Jit,
    m0: *mut u32,
    registers: &mut Registers,
) -> c_int {
    assert!(is_aligned(registers.ep));
    let mut inner = jit.0.take().expect("Trying to call run() after error");
    *inner.global_mut(Global(0)) = Word {mp: (registers as *mut Registers).cast()};
    *inner.global_mut(Global(1)) = Word {mp: m0.cast()};
    *inner.global_mut(Global(2)) = Word {u: 0xDEADDEADDEADDEAD};
    *inner.global_mut(Global(3)) = Word {u: 0xDEADDEADDEADDEAD};
    let (inner, trap) = inner.execute(&State::Root).expect("Execute failed");
    jit.0 = Some(inner);
    match trap {
        Trap::Halt => {
            // Pop the HALT code.
            assert!(is_aligned(registers.sp));
            let halt_code = std::ptr::read(m0.offset((registers.sp >> 2).try_into().unwrap()));
            registers.sp += CELL;
            halt_code as c_int
        },
        Trap::NotImplemented => -511,
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
}
