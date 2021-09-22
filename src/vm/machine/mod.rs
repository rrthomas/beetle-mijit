/*! The `mijit::code::Machine` that provides the performance-critical part. */

use std::num::{Wrapping};
use memoffset::{offset_of};
use mijit::code::{
    self, UnaryOp, BinaryOp, Global, Slot, Register, REGISTERS, Variable,
    Switch, Case, Convention, Marshal,
};
use UnaryOp::*;
use BinaryOp::*;

use super::{Registers, AllRegisters, cell_bytes};

/** The number of bits in a word. */
pub const CELL_BITS: i64 = cell_bytes(8);

//-----------------------------------------------------------------------------

/* Register allocation. */

const NUM_SLOTS: usize = 4;

const TEMP: Register = REGISTERS[0];
const R1: Register = REGISTERS[1];
const R2: Register = REGISTERS[2];
const R3: Register = REGISTERS[3];
const R4: Register = REGISTERS[4];
const R5: Register = REGISTERS[5];

const BEP: Variable = Variable::Register(REGISTERS[6]);
const BA: Variable = Variable::Register(REGISTERS[7]);
const BSP: Variable = Variable::Register(REGISTERS[8]);
const BRP: Variable = Variable::Register(REGISTERS[9]);
const MEMORY: Variable = Variable::Register(REGISTERS[10]);
const OPCODE: Variable = Variable::Register(REGISTERS[11]);
const STACK0: Variable = Variable::Slot(Slot(0));
const STACK1: Variable = Variable::Slot(Slot(1));
const LOOP_NEW: Variable = Variable::Slot(Slot(2));
const LOOP_OLD: Variable = Variable::Slot(Slot(3));

//-----------------------------------------------------------------------------

/* Control-flow states. */

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum State {
    Root,
    Dispatch,
    Next,
    Pick,
    Roll,
    Qdup,
    Lshift,
    Rshift,
    Branch,
    Branchi,
    Qbranch,
    Qbranchi,
    Loop,
    Loopi,
    PloopTest,
    Ploop,
    PloopiTest,
    Ploopi,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Trap {
    Halt,
    NotImplemented,
}

//-----------------------------------------------------------------------------

mod builder;
use builder::{build, Builder};

/** Returns the offset of `$field`. */
macro_rules! private_register {
    ($field: ident) => {
        offset_of!(AllRegisters, $field)
    }
}

/** Returns the offset of `$field`. */
macro_rules! public_register {
    ($field: ident) => {
        offset_of!(AllRegisters, public) + offset_of!(Registers, $field)
    }
}

/** The performance-critical part of the virtual machine. */
#[derive(Debug)]
pub struct Machine;

impl code::Machine for Machine {
    type State = State;

    type Trap = Trap;

    fn num_globals(&self) -> usize { 1 }

    fn marshal(&self, state: Self::State) -> Marshal {
        let mut live_values = vec![Global(0).into(), BEP, BSP, BRP, MEMORY];
        #[allow(clippy::match_same_arms)]
        live_values.extend(match state {
            State::Root => vec![BA],
            State::Next => vec![],
            State::Pick => vec![BA, STACK0],
            State::Roll => vec![BA, STACK0],
            State::Qdup => vec![BA, STACK0],
            State::Lshift => vec![BA, OPCODE, STACK0, STACK1],
            State::Rshift => vec![BA, OPCODE, STACK0, STACK1],
            State::Branch => vec![],
            State::Branchi => vec![BA],
            State::Qbranch => vec![BA, STACK0],
            State::Qbranchi => vec![BA, STACK0],
            State::Loop => vec![BA, OPCODE],
            State::Loopi => vec![BA, OPCODE],
            State::PloopTest => vec![BA, OPCODE],
            State::Ploop => vec![BA, OPCODE, LOOP_NEW, LOOP_OLD],
            State::PloopiTest => vec![BA, OPCODE],
            State::Ploopi => vec![BA, OPCODE, LOOP_NEW, LOOP_OLD],
            State::Dispatch => vec![BA, OPCODE],
        });
        let prologue = {
            let mut b = Builder::new();
            b.add_slots(NUM_SLOTS);
            b.load_register(BEP, public_register!(ep));
            b.load_register(BA, public_register!(a));
            b.load_register(BSP, public_register!(sp));
            b.load_register(BRP, public_register!(rp));
            b.load_register64(MEMORY, private_register!(memory));
            b.load_register(OPCODE, private_register!(opcode));
            b.load_register(STACK0, private_register!(stack0));
            b.load_register(STACK1, private_register!(stack1));
            b.load_register(LOOP_NEW, private_register!(loop_new));
            b.load_register(LOOP_OLD, private_register!(loop_old));
            b.finish()
        };
        let epilogue = {
            let mut b = Builder::new();
            for v in [BA, OPCODE, STACK0, STACK1, LOOP_NEW, LOOP_OLD] {
                if !live_values.contains(&v) {
                    b.const64(v, 0xDEADDEADDEADDEADu64 as i64);
                }
            }
            b.store_register(BEP, public_register!(ep));
            b.store_register(BA, public_register!(a));
            b.store_register(BSP, public_register!(sp));
            b.store_register(BRP, public_register!(rp));
            b.store_register64(MEMORY, private_register!(memory));
            b.store_register(OPCODE, private_register!(opcode));
            b.store_register(STACK0, private_register!(stack0));
            b.store_register(STACK1, private_register!(stack1));
            b.store_register(LOOP_NEW, private_register!(loop_new));
            b.store_register(LOOP_OLD, private_register!(loop_old));
            b.remove_slots(NUM_SLOTS);
            b.finish()
        };
        let convention = Convention {
            slots_used: NUM_SLOTS,
            live_values: live_values.into(),
        };
        Marshal {prologue, convention, epilogue}
    }

    #[allow(clippy::too_many_lines)]
    fn code(&self, state: Self::State) -> Switch<Case<Result<Self::State, Self::Trap>>> {
        match state {
            State::Root => Switch::always(build(|b| {
                b.const_binary(And, OPCODE, BA, 0xFF);
                b.const_binary(Asr, BA, BA, 8);
            }, Ok(State::Dispatch))),
            State::Next => Switch::always(build(|b| {
                b.pop(BA, BEP);
            }, Ok(State::Root))),
            State::Pick => Switch::new(
                STACK0,
                (0..4).map(|u| build(|b| {
                    b.const_binary(Add, R2, BSP, cell_bytes(i64::from(u) + 1));
                    b.load(R2, R2);
                    b.store(R2, BSP);
                }, Ok(State::Root))).collect(),
                build(|_| {}, Err(Trap::Halt)),
            ),
            State::Roll => Switch::new(
                STACK0,
                (0..4).map(|u| build(|b| {
                    b.const_binary(Add, R5, BSP, cell_bytes(u));
                    b.load(R3, R5);
                    for v in 0..u {
                        b.const_binary(Add, R4, BSP, cell_bytes(v));
                        b.load(R2, R4);
                        b.store(R3, R4);
                        b.move_(R3, R2);
                    }
                    b.store(R3, R5);
                }, Ok(State::Root))).collect(),
                build(|_| {}, Err(Trap::Halt)),
            ),
            State::Qdup => Switch::if_(
                STACK0,
                build(|b| {
                    b.push(STACK0, BSP);
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Root)),
            ),
            State::Lshift => Switch::if_(
                OPCODE, // `Ult(STACK0, CELL_BITS)`
                build(|b| {
                    b.binary(Lsl, R2, STACK0, STACK1);
                    b.store(R2, BSP);
                }, Ok(State::Root)),
                build(|b| {
                    b.const_(R2, 0);
                    b.store(R2, BSP);
                }, Ok(State::Root)),
            ),
            State::Rshift => Switch::if_(
                OPCODE, // `Ult(STACK0, CELL_BITS)`
                build(|b| {
                    b.binary(Lsr, R2, STACK0, STACK1);
                    b.store(R2, BSP);
                }, Ok(State::Root)),
                build(|b| {
                    b.const_(R2, 0);
                    b.store(R2, BSP);
                }, Ok(State::Root)),
            ),
            State::Branch => Switch::always(build(|b| {
                // Load EP from the cell it points to.
                b.load(BEP, BEP); // FIXME: Add check that EP is valid.
            }, Ok(State::Next))),
            State::Branchi => Switch::always(build(|b| {
                b.const_binary(Mul, R2, BA, cell_bytes(1));
                b.binary(Add, BEP, BEP, R2); // FIXME: Add check that EP is valid.
            }, Ok(State::Next))),
            State::Qbranch => Switch::if_(
                STACK0,
                build(|b| {
                    b.const_binary(Add, BEP, BEP, cell_bytes(1));
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Branch)),
            ),
            State::Qbranchi => Switch::if_(
                STACK0,
                build(|_| {}, Ok(State::Next)),
                build(|_| {}, Ok(State::Branchi)),
            ),
            State::Loop => Switch::if_(
                OPCODE, // zero to exit the loop
                build(|_| {}, Ok(State::Branch)),
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                    // Add 4 to EP.
                    b.const_binary(Add, BEP, BEP, cell_bytes(1)); // FIXME: Add check that EP is valid.
                }, Ok(State::Root)),
            ),
            State::Loopi => Switch::if_(
                OPCODE, // zero to exit the loop
                build(|_| {}, Ok(State::Branchi)),
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                }, Ok(State::Next)),
            ),
            State::PloopTest => Switch::if_(
                OPCODE, // non-zero to exit the loop
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                    // Add 4 to EP.
                    b.const_binary(Add, BEP, BEP, cell_bytes(1)); // FIXME: Add check that EP is valid.
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Branch)),
            ),
            State::Ploop => Switch::if_(
                OPCODE, // Lt(step, 0)
                build(|b| {
                    b.unary(Not, LOOP_OLD, LOOP_OLD);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                    b.const_binary(Lt, OPCODE, LOOP_NEW, 0);
                }, Ok(State::PloopTest)),
                build(|b| {
                    b.unary(Not, LOOP_NEW, LOOP_NEW);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                    b.const_binary(Lt, OPCODE, LOOP_NEW, 0);
                }, Ok(State::PloopTest)),
            ),
            State::PloopiTest => Switch::if_(
                OPCODE, // non-zero to exit the loop
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, cell_bytes(2));
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Branchi)),
            ),
            State::Ploopi => Switch::if_(
                OPCODE, // Lt(step, 0)
                build(|b| {
                    b.unary(Not, LOOP_OLD, LOOP_OLD);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                    b.const_binary(Lt, OPCODE, LOOP_NEW, 0);
                }, Ok(State::PloopiTest)),
                build(|b| {
                    b.unary(Not, LOOP_NEW, LOOP_NEW);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                    b.const_binary(Lt, OPCODE, LOOP_NEW, 0);
                }, Ok(State::PloopiTest)),
            ),
            State::Dispatch => Switch::new(
                OPCODE,
                Box::new([
                    // NEXT
                    build(|_| {}, Ok(State::Next)),

                    // DUP
                    build(|b| {
                        b.load(R2, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // DROP
                    build(|b| {
                        b.const_binary(Add, BSP, BSP, cell_bytes(1));
                    }, Ok(State::Root)),

                    // SWAP
                    build(|b| {
                        b.pop(R4, BSP);
                        b.load(R3, BSP);
                        b.store(R4, BSP);
                        b.push(R3, BSP);
                    }, Ok(State::Root)),

                    // OVER
                    build(|b| {
                        b.const_binary(Add, R2, BSP, cell_bytes(1));
                        b.load(R3, R2);
                        b.push(R3, BSP);
                    }, Ok(State::Root)),

                    // ROT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R5, BSP, cell_bytes(1));
                        b.load(R3, R5);
                        b.store(R2, R5);
                        b.const_binary(Add, R5, BSP, cell_bytes(2));
                        b.load(R2, R5);
                        b.store(R3, R5);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // -ROT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R5, BSP, cell_bytes(2));
                        b.load(R3, R5);
                        b.store(R2, R5);
                        b.const_binary(Add, R5, BSP, cell_bytes(1));
                        b.load(R2, R5);
                        b.store(R3, R5);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // TUCK
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R5, BSP, cell_bytes(1));
                        b.load(R3, R5);
                        b.store(R2, R5);
                        b.store(R3, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // NIP
                    build(|b| {
                        b.pop(R2, BSP);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // PICK
                    build(|b| {
                        b.load(STACK0, BSP);
                    }, Ok(State::Pick)),

                    // ROLL
                    build(|b| {
                        b.pop(STACK0, BSP);
                    }, Ok(State::Roll)),

                    // ?DUP
                    build(|b| {
                        b.load(STACK0, BSP);
                    }, Ok(State::Qdup)),

                    // >R
                    build(|b| {
                        b.pop(R2, BSP);
                        b.push(R2, BRP);
                    }, Ok(State::Root)),

                    // R>
                    build(|b| {
                        b.pop(R2, BRP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // R@
                    build(|b| {
                        b.load(R2, BRP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // <
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Lt, R2, R4, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // >
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Lt, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // =
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Eq, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // <>
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Eq, R2, R2, R4);
                        b.unary(Not, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0<
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Lt, R2, R2, 0);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0>
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_(R4, 0);
                        b.binary(Lt, R2, R4, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0=
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Eq, R2, R2, 0);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0<>
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Eq, R2, R2, 0);
                        b.unary(Not, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // U<
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Ult, R2, R4, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // U>
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Ult, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0
                    build(|b| {
                        b.const_(R4, 0);
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // 1
                    build(|b| {
                        b.const_(R4, 1);
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // -1
                    build(|b| {
                        b.const_(R4, -1);
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // CELL
                    build(|b| {
                        b.const_(R4, cell_bytes(1));
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // -CELL
                    build(|b| {
                        b.const_(R4, (-Wrapping(cell_bytes(1))).0);
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // +
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Add, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // -
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Sub, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // >-<
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Sub, R2, R4, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 1+
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 1-
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Sub, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // CELL+
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R2, R2, cell_bytes(1));
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // CELL-
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Sub, R2, R2, cell_bytes(1));
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // *
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Mul, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // /
                    build(|_| {
                        // TODO
                    }, Err(Trap::NotImplemented)),

                    // MOD
                    build(|_| {
                        // TODO
                    }, Err(Trap::NotImplemented)),

                    // /MOD
                    build(|_| {
                        // TODO
                    }, Err(Trap::NotImplemented)),

                    // U/MOD
                    build(|_| {
                        // TODO
                    }, Err(Trap::NotImplemented)),

                    // S/REM
                    build(|_| {
                        // TODO
                    }, Err(Trap::NotImplemented)),

                    // 2/
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Asr, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // CELLS
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Mul, R2, R2, cell_bytes(1));
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // ABS
                    build(|b| {
                        b.load(R2, BSP);
                        b.unary(Abs, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // NEGATE
                    build(|b| {
                        b.load(R2, BSP);
                        b.unary(Negate, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // MAX
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Max, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // MIN
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Min, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // INVERT
                    build(|b| {
                        b.load(R2, BSP);
                        b.unary(Not, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // AND
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(And, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // OR
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Or, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // XOR
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R4, BSP);
                        b.binary(Xor, R2, R2, R4);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // LSHIFT
                    build(|b| {
                        b.pop(STACK0, BSP);
                        b.load(STACK1, BSP);
                        b.const_binary(Ult, OPCODE, STACK1, CELL_BITS);
                    }, Ok(State::Lshift)),

                    // RSHIFT
                    build(|b| {
                        b.pop(STACK0, BSP);
                        b.load(STACK1, BSP);
                        b.const_binary(Ult, OPCODE, STACK1, CELL_BITS);
                    }, Ok(State::Rshift)),

                    // 1LSHIFT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Lsl, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 1RSHIFT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Lsr, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // @
                    build(|b| {
                        b.load(R2, BSP);
                        b.load(R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // !
                    build(|b| {
                        b.pop(R2, BSP);
                        b.pop(R3, BSP);
                        b.store(R3, R2);
                    }, Ok(State::Root)),

                    // C@
                    build(|b| {
                        b.load(R2, BSP);
                        b.load_byte(R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // C!
                    build(|b| {
                        b.pop(R2, BSP);
                        b.pop(R3, BSP);
                        b.store_byte(R3, R2);
                    }, Ok(State::Root)),

                    // +!
                    build(|b| {
                        b.pop(R2, BSP);
                        b.pop(R3, BSP);
                        b.load(R5, R2);
                        b.binary(Add, R3, R5, R3);
                        b.store(R3, R2);
                    }, Ok(State::Root)),

                    // BSP@
                    build(|b| {
                        b.move_(R1, BSP);
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // BSP!
                    build(|b| {
                        b.load(BSP, BSP);
                    }, Ok(State::Root)),

                    // BRP@
                    build(|b| {
                        b.push(BRP, BSP);
                    }, Ok(State::Root)),

                    // BRP!
                    build(|b| {
                        b.pop(BRP, BSP);
                    }, Ok(State::Root)),

                    // EP@
                    build(|b| {
                        b.push(BEP, BSP);
                    }, Ok(State::Root)),

                    // BS0@
                    build(|b| {
                        b.load_register(R1, public_register!(s0));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // BS0!
                    build(|b| {
                        b.pop(R1, BSP);
                        b.store_register(R1, public_register!(s0));
                    }, Ok(State::Root)),

                    // BR0@
                    build(|b| {
                        b.load_register(R1, public_register!(r0));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // BR0!
                    build(|b| {
                        b.pop(R1, BSP);
                        b.store_register(R1, public_register!(r0));
                    }, Ok(State::Root)),

                    // 'THROW@
                    build(|b| {
                        b.load_register(R1, public_register!(throw));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // 'THROW!
                    build(|b| {
                        b.pop(R1, BSP);
                        b.store_register(R1, public_register!(throw));
                    }, Ok(State::Root)),

                    // MEMORY@
                    build(|b| {
                        b.load_register(R1, private_register!(memory));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // 'BAD@
                    build(|b| {
                        b.load_register(R1, public_register!(bad));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // -ADDRESS@
                    build(|b| {
                        b.load_register(R1, public_register!(not_address));
                        b.push(R1, BSP);
                    }, Ok(State::Root)),

                    // BRANCH
                    build(|_| {}, Ok(State::Branch)),

                    // BRANCHI
                    build(|_| {}, Ok(State::Branchi)),

                    // ?BRANCH
                    build(|b| {
                        b.pop(STACK0, BSP);
                    }, Ok(State::Qbranch)),

                    // ?BRANCHI
                    build(|b| {
                        b.pop(STACK0, BSP);
                    }, Ok(State::Qbranchi)),

                    // EXECUTE
                    build(|b| {
                        b.push(BEP, BRP);
                        b.pop(BEP, BSP); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // @EXECUTE
                    build(|b| {
                        b.push(BEP, BRP);
                        b.pop(R1, BSP);
                        b.load(BEP, R1); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // CALL
                    build(|b| {
                        b.const_binary(Add, R1, BEP, cell_bytes(1));
                        b.push(R1, BRP);
                    }, Ok(State::Branch)),

                    // CALLI
                    build(|b| {
                        b.push(BEP, BRP);
                    }, Ok(State::Branchi)),

                    // EXIT
                    build(|b| {
                        b.pop(BEP, BRP); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // (DO)
                    build(|b| {
                        // Pop two items from SP.
                        b.pop(R4, BSP);
                        b.pop(R3, BSP);
                        // Push two items to RP.
                        b.push(R3, BRP);
                        b.push(R4, BRP);
                    }, Ok(State::Root)),

                    // (LOOP)
                    build(|b| {
                        // Load the index and limit from RP.
                        b.pop(R3, BRP);
                        b.load(R4, BRP);
                        // Update the index.
                        b.const_binary(Add, R3, R3, 1);
                        b.push(R3, BRP);
                        b.binary(Sub, OPCODE, R3, R4);
                    }, Ok(State::Loop)),

                    // (LOOP)I
                    build(|b| {
                        // Load the index and limit from RP.
                        b.pop(R3, BRP);
                        b.load(R4, BRP);
                        // Update the index.
                        b.const_binary(Add, R3, R3, 1);
                        b.push(R3, BRP);
                        b.binary(Sub, OPCODE, R3, R4);
                    }, Ok(State::Loopi)),

                    // (+LOOP)
                    build(|b| {
                        // Pop the step from SP.
                        b.pop(R1, BSP);
                        // Load the index and limit from RP.
                        b.pop(R3, BRP);
                        b.load(R4, BRP);
                        // Update the index.
                        b.binary(Add, R5, R3, R1);
                        b.push(R5, BRP);
                        // Compute the differences between old and new indexes and limit.
                        b.binary(Sub, LOOP_OLD, R3, R4);
                        b.binary(Sub, LOOP_NEW, R5, R4);
                        // Is the step negative?
                        b.const_binary(Lt, OPCODE, R1, 0);
                    }, Ok(State::Ploop)),

                    // (+LOOP)I
                    build(|b| {
                        // Pop the step from SP.
                        b.pop(R1, BSP);
                        // Load the index and limit from RP.
                        b.pop(R3, BRP);
                        b.load(R4, BRP);
                        // Update the index.
                        b.binary(Add, R5, R3, R1);
                        b.push(R5, BRP);
                        // Compute the differences between old and new indexes and limit.
                        b.binary(Sub, LOOP_OLD, R3, R4);
                        b.binary(Sub, LOOP_NEW, R5, R4);
                        // Is the step negative?
                        b.const_binary(Lt, OPCODE, R1, 0);
                    }, Ok(State::Ploopi)),

                    // UNLOOP
                    build(|b| {
                        // Discard two items from RP.
                        b.const_binary(Add, BRP, BRP, cell_bytes(2));
                    }, Ok(State::Root)),

                    // J
                    build(|b| {
                        // Push the third item of RP to SP.
                        b.const_binary(Add, R1, BRP, cell_bytes(2));
                        b.load(R4, R1);
                        b.push(R4, BSP);
                    }, Ok(State::Root)),

                    // (LITERAL)
                    build(|b| {
                        // Load R2 from cell pointed to by BEP, and add 4 to EP.
                        b.pop(R2, BEP); // FIXME: Add check that EP is now valid.
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // (LITERAL)I
                    build(|b| {
                        b.push(BA, BSP);
                    }, Ok(State::Next)),

                    // THROW
                    build(|b| {
                        b.store_register(BEP, public_register!(bad));
                        b.load_register(BEP, public_register!(throw)); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // HALT
                    build(|_| {}, Err(Trap::Halt)),
                ]),
                build(|_| {}, Err(Trap::Halt)),
            ),
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Root]
    }
}