use mijit::target::{Native, native, Word};
use mijit::code::{Global};

#[allow(unused)]
mod mijit_builder;

mod machine;
use machine::{Registers, VM};

/** The state of the JIT compiler. */
type Jit = VM<Native>;

/** Indicate whether an address is cell-aligned. */
fn is_aligned(addr: u32) -> bool {
    addr & 0x3 == 0
}

/** Allocates a new Jit. */
#[no_mangle]
pub extern fn mijit_beetle_new() -> Box<Jit> {
    Box::new(VM::new(native()))
}

/** Frees a Jit. */
#[no_mangle]
pub extern fn mijit_beetle_drop(_vm: Box<Jit>) {}

/** Run the code at address `registers.ep`. */
#[no_mangle]
pub unsafe extern fn mijit_beetle_run(jit: &mut Jit, m0: *mut u32, registers: &mut Registers) {
    assert!(is_aligned(registers.ep));
    *jit.global_mut(Global(0)) = Word {mp: (registers as *mut Registers).cast()};
    *jit.global_mut(Global(1)) = Word {mp: m0.cast()};
    *jit.global_mut(Global(2)) = Word {u: 0xDEADDEADDEADDEAD};
    *jit.global_mut(Global(3)) = Word {u: 0xDEADDEADDEADDEAD};
    jit.run();
}
