/*! The `mijit::code::Machine` that provides the performance-critical part. */

use std::num::{Wrapping};
use memoffset::{offset_of};
use mijit::code::{
    self, UnaryOp, BinaryOp, Global, Register, REGISTERS, Variable,
    Switch, Case, Convention, Marshal,
};
use UnaryOp::*;
use BinaryOp::*;

use super::{Registers, AllRegisters};

/** The number of bytes in a cell. */
pub const CELL: u32 = 4;

/** The number of bits in a word. */
pub const CELL_BITS: u32 = CELL * 8;

//-----------------------------------------------------------------------------

/* Register allocation. */

const TEMP: Register = REGISTERS[0];
const R1: Register = REGISTERS[1];
const R2: Register = REGISTERS[2];
const R3: Register = REGISTERS[3];
const BEP: Register = REGISTERS[4];
const BI: Register = REGISTERS[5];
const BA: Register = REGISTERS[6];
const BSP: Register = REGISTERS[7];
const BRP: Register = REGISTERS[8];
const M0: Register = REGISTERS[9];

//-----------------------------------------------------------------------------

/* Control-flow states. */

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum State {
    Root,
    Dispatch,
    Next,
    Throw,
    Pick,
    Roll,
    Qdup,
    DivTest,
    Divide,
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
    Lib,
    Undefined,
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
        let mut live_values = vec![Global(0).into(), BEP.into(), BSP.into(), BRP.into(), M0.into()];
        #[allow(clippy::match_same_arms)]
        live_values.extend(match state {
            State::Root => vec![BA],
            State::Next => vec![],
            State::Throw => vec![],
            State::Pick => vec![BA, R2],
            State::Roll => vec![BA, R2],
            State::Qdup => vec![BA, R2],
            State::DivTest => vec![BA, BI, R2],
            State::Divide => vec![BA, BI, R2],
            State::Lshift => vec![BA, BI, R2, R3],
            State::Rshift => vec![BA, BI, R2, R3],
            State::Branch => vec![],
            State::Branchi => vec![BA],
            State::Qbranch => vec![BA, R2],
            State::Qbranchi => vec![BA, R2],
            State::Loop => vec![BA, BI],
            State::Loopi => vec![BA, BI],
            State::PloopTest => vec![BA, BI],
            State::Ploop => vec![BA, BI, R2, R3],
            State::PloopiTest => vec![BA, BI],
            State::Ploopi => vec![BA, BI, R2, R3],
            State::Dispatch => vec![BA, BI],
        }.into_iter().map(Variable::Register));
        let prologue = {
            let mut b = Builder::new();
            b.load_register(BEP, public_register!(ep));
            b.load_register(BI, public_register!(i));
            b.load_register(BA, public_register!(a));
            b.load_register(BSP, public_register!(sp));
            b.load_register(BRP, public_register!(rp));
            b.load_register64(M0, private_register!(m0));
            b.load_register(R2, private_register!(r2));
            b.load_register(R3, private_register!(r3));
            b.finish()
        };
        let epilogue = {
            let mut b = Builder::new();
            for v in [BA, BI, R2, R3] {
                if !live_values.contains(&Variable::Register(v)) {
                    b.const64(v, 0xDEADDEADDEADDEADu64);
                }
            }
            b.store_register(BEP, public_register!(ep));
            b.store_register(BI, public_register!(i));
            b.store_register(BA, public_register!(a));
            b.store_register(BSP, public_register!(sp));
            b.store_register(BRP, public_register!(rp));
            b.store_register64(M0, private_register!(m0));
            b.store_register(R2, private_register!(r2));
            b.store_register(R3, private_register!(r3));
            b.finish()
        };
        let convention = Convention {
            slots_used: 0,
            live_values: live_values.into(),
        };
        Marshal {prologue, convention, epilogue}
    }

    #[allow(clippy::too_many_lines)]
    fn code(&self, state: Self::State) -> Switch<Case<Result<Self::State, Self::Trap>>> {
        match state {
            State::Root => Switch::always(build(|b| {
                b.const_binary(And, BI, BA, 0xFF);
                b.const_binary(Asr, BA, BA, 8);
            }, Ok(State::Dispatch))),
            State::Next => Switch::always(build(|b| {
                b.pop(BA, BEP);
            }, Ok(State::Root))),
            State::Throw => Switch::always(build(|b| {
                b.store_register(BEP, public_register!(bad));
                b.load_register(BEP, public_register!(throw)); // FIXME: Add check that EP is valid.
            }, Ok(State::Next))),
            State::Pick => Switch::new(
                R2.into(),
                (0..4).map(|u| build(|b| {
                    b.const_binary(Add, R1, BSP, (u + 1) * CELL);
                    b.load(R2, R1);
                    b.store(R2, BSP);
                }, Ok(State::Root))).collect(),
                build(|_| {}, Err(Trap::Halt)),
            ),
            State::Roll => Switch::new(
                R2.into(),
                (0..4).map(|u| build(|b| {
                    b.const_binary(Add, R1, BSP, u * CELL);
                    b.load(R3, R1);
                    for v in 0..u {
                        b.const_binary(Add, R1, BSP, v * CELL);
                        b.load(R2, R1);
                        b.store(R3, R1);
                        b.move_(R3, R2);
                    }
                    b.const_binary(Add, R1, BSP, u * CELL);
                    b.store(R3, R1);
                }, Ok(State::Root))).collect(),
                build(|_| {}, Err(Trap::Halt)),
            ),
            State::Qdup => Switch::if_(
                R2.into(),
                build(|b| {
                    b.push(R2, BSP);
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Root)),
            ),
            State::DivTest => Switch::if_(
                R2.into(), // denominator.
                build(|b| {
                    b.const_binary(Sub, BI, BI, 0x26); // FIXME: Symbolic constant.
                    b.load(R3, BSP);
                }, Ok(State::Divide)),
                build(|b| {
                    b.const_(R2, -10i32 as u32); // Division by zero.
                    b.store(R2, BSP);
                }, Ok(State::Throw)),
            ),
            State::Divide => Switch::new(
                BI.into(), // Beetle opcode - 0x26. FIXME: Symbolic constant.
                Box::new([
                    // /
                    build(|b| {
                        // If denominator (`R2`) is negative,
                        // negate numerator (`R3`) and denominator.
                        b.const_binary(Asr, BI, R2, 31);
                        b.binary(Xor, R1, R3, BI);
                        b.binary(Sub, R3, R1, BI);
                        b.binary(Xor, R2, R2, BI);
                        b.binary(Sub, R2, R2, BI);
                        // If the numerator is negative, invert it.
                        // If `R3` is `0x80000000` it can be positive or
                        // negative depending on whether `R3` was negated.
                        // So test `R1 < BI`, not `R3 < 0`.
                        b.binary(Lt, BI, R1, BI);
                        b.binary(Xor, R3, R3, BI);
                        // Now both `R3` and `R2` are non-negative. Use `UDiv`.
                        b.binary(UDiv, R2, R3, R2);
                        // If the numerator was negative, invert the quotient.
                        b.binary(Xor, R2, R2, BI);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),
                    // MOD
                    build(|b| {
                        // See "/".
                        b.const_binary(Asr, BI, R2, 31);
                        b.binary(Xor, R1, R3, BI);
                        b.binary(Sub, R3, R1, BI);
                        b.binary(Xor, R2, R2, BI);
                        b.binary(Sub, R2, R2, BI);
                        b.binary(Lt, BI, R1, BI);
                        b.binary(Xor, R3, R3, BI);
                        b.binary(UDiv, R2, R3, R2);
                        b.binary(Xor, R2, R2, BI);
                        // Compute remainder.
                        b.const_binary(Sub, R1, BSP, CELL);
                        b.load(R1, R1);
                        b.load(R3, BSP);
                        b.binary(Mul, R1, R2, R1);
                        b.binary(Sub, R3, R3, R1);
                        b.store(R3, BSP);
                    }, Ok(State::Root)),
                    // /MOD
                    build(|b| {
                        // See "/".
                        b.const_binary(Asr, BI, R2, 31);
                        b.binary(Xor, R1, R3, BI);
                        b.binary(Sub, R3, R1, BI);
                        b.binary(Xor, R2, R2, BI);
                        b.binary(Sub, R2, R2, BI);
                        b.binary(Lt, BI, R1, BI);
                        b.binary(Xor, R3, R3, BI);
                        b.binary(UDiv, R2, R3, R2);
                        b.binary(Xor, R2, R2, BI);
                        // Compute remainder.
                        b.const_binary(Sub, R1, BSP, CELL);
                        b.load(R1, R1);
                        b.load(R3, BSP);
                        b.binary(Mul, R1, R2, R1);
                        b.binary(Sub, R3, R3, R1);
                        b.store(R3, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),
                    // U/MOD
                    build(|b| {
                        b.binary(UDiv, R2, R3, R2);
                        // Compute remainder.
                        b.const_binary(Sub, R1, BSP, CELL);
                        b.load(R1, R1);
                        b.load(R3, BSP);
                        b.binary(Mul, R1, R2, R1);
                        b.binary(Sub, R3, R3, R1);
                        b.store(R3, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),
                    // S/REM
                    build(|b| {
                        // Cannot use Mijit's `SDiv` because of the case
                        // `-2³¹ / -1` which is undefined behaviour in Mijit
                        // but not in Beetle. So use `UDiv` instead.
                        // If denominator (`R2`) is negative,
                        // negate numerator (`R3`) and denominator.
                        b.const_binary(Asr, BI, R2, 31);
                        b.binary(Xor, R1, R3, BI);
                        b.binary(Sub, R3, R1, BI);
                        b.binary(Xor, R2, R2, BI);
                        b.binary(Sub, R2, R2, BI);
                        // If the numerator is negative, negate it.
                        // If `R3` is `0x80000000` it can be positive or
                        // negative depending on whether `R3` was negated.
                        // So test `R1 < BI`, not `R3 < 0`.
                        b.binary(Lt, BI, R1, BI);
                        b.binary(Xor, R3, R3, BI);
                        b.binary(Sub, R3, R3, BI);
                        // Now both `R3` and `R2` are non-negative. Use `UDiv`.
                        b.binary(UDiv, R2, R3, R2);
                        // If the numerator was negative, invert the quotient.
                        b.binary(Xor, R2, R2, BI);
                        b.binary(Sub, R2, R2, BI);
                        // Compute remainder.
                        b.const_binary(Sub, R1, BSP, CELL);
                        b.load(R1, R1);
                        b.load(R3, BSP);
                        b.binary(Mul, R1, R2, R1);
                        b.binary(Sub, R3, R3, R1);
                        b.store(R3, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),
                ]),
                build(|b| {
                    // Restore the `BI`.
                    b.const_binary(Add, BI, BI, 0x26); // FIXME: Symbolic constant.
                }, Err(Trap::NotImplemented)), // Should not happen.
            ),
            State::Lshift => Switch::if_(
                BI.into(), // `Ult(R2, CELL_BITS)`
                build(|b| {
                    b.binary(Lsl, R2, R3, R2);
                    b.store(R2, BSP);
                }, Ok(State::Root)),
                build(|b| {
                    b.const_(R2, 0);
                    b.store(R2, BSP);
                }, Ok(State::Root)),
            ),
            State::Rshift => Switch::if_(
                BI.into(), // `Ult(R2, CELL_BITS)`
                build(|b| {
                    b.binary(Lsr, R2, R3, R2);
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
                b.const_binary(Mul, R1, BA, CELL);
                b.binary(Add, BEP, BEP, R1); // FIXME: Add check that EP is valid.
            }, Ok(State::Next))),
            State::Qbranch => Switch::if_(
                R2.into(),
                build(|b| {
                    b.const_binary(Add, BEP, BEP, CELL);
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Branch)),
            ),
            State::Qbranchi => Switch::if_(
                R2.into(),
                build(|_| {}, Ok(State::Next)),
                build(|_| {}, Ok(State::Branchi)),
            ),
            State::Loop => Switch::if_(
                BI.into(), // zero to exit the loop
                build(|_| {}, Ok(State::Branch)),
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, 2 * CELL);
                    // Add 4 to EP.
                    b.const_binary(Add, BEP, BEP, CELL); // FIXME: Add check that EP is valid.
                }, Ok(State::Root)),
            ),
            State::Loopi => Switch::if_(
                BI.into(), // zero to exit the loop
                build(|_| {}, Ok(State::Branchi)),
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, 2 * CELL);
                }, Ok(State::Next)),
            ),
            State::PloopTest => Switch::if_(
                BI.into(), // non-zero to exit the loop
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, 2 * CELL);
                    // Add 4 to EP.
                    b.const_binary(Add, BEP, BEP, CELL); // FIXME: Add check that EP is valid.
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Branch)),
            ),
            State::Ploop => Switch::if_(
                BI.into(), // Lt(step, 0)
                build(|b| {
                    b.unary(Not, R2, R2);
                    b.binary(And, R3, R3, R2);
                    b.const_binary(Lt, BI, R3, 0);
                }, Ok(State::PloopTest)),
                build(|b| {
                    b.unary(Not, R3, R3);
                    b.binary(And, R3, R3, R2);
                    b.const_binary(Lt, BI, R3, 0);
                }, Ok(State::PloopTest)),
            ),
            State::PloopiTest => Switch::if_(
                BI.into(), // non-zero to exit the loop
                build(|b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, BRP, BRP, 2 * CELL);
                }, Ok(State::Next)),
                build(|_| {}, Ok(State::Branchi)),
            ),
            State::Ploopi => Switch::if_(
                BI.into(), // Lt(step, 0)
                build(|b| {
                    b.unary(Not, R2, R2);
                    b.binary(And, R3, R3, R2);
                    b.const_binary(Lt, BI, R3, 0);
                }, Ok(State::PloopiTest)),
                build(|b| {
                    b.unary(Not, R3, R3);
                    b.binary(And, R3, R3, R2);
                    b.const_binary(Lt, BI, R3, 0);
                }, Ok(State::PloopiTest)),
            ),
            State::Dispatch => Switch::new(
                BI.into(),
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
                        b.const_binary(Add, BSP, BSP, CELL);
                    }, Ok(State::Root)),

                    // SWAP
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.store(R2, BSP);
                        b.push(R3, BSP);
                    }, Ok(State::Root)),

                    // OVER
                    build(|b| {
                        b.const_binary(Add, R1, BSP, CELL);
                        b.load(R2, R1);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // ROT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R1, BSP, CELL);
                        b.load(R3, R1);
                        b.store(R2, R1);
                        b.const_binary(Add, R1, BSP, 2 * CELL);
                        b.load(R2, R1);
                        b.store(R3, R1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // -ROT
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R1, BSP, 2 * CELL);
                        b.load(R3, R1);
                        b.store(R2, R1);
                        b.const_binary(Add, R1, BSP, CELL);
                        b.load(R2, R1);
                        b.store(R3, R1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // TUCK
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R1, BSP, CELL);
                        b.load(R3, R1);
                        b.store(R2, R1);
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
                        b.load(R2, BSP);
                    }, Ok(State::Pick)),

                    // ROLL
                    build(|b| {
                        b.pop(R2, BSP);
                    }, Ok(State::Roll)),

                    // ?DUP
                    build(|b| {
                        b.load(R2, BSP);
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
                        b.load(R3, BSP);
                        b.binary(Lt, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // >
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Lt, R2, R2, R3);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // =
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Eq, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // <>
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Eq, R2, R3, R2);
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
                        b.const_(R3, 0);
                        b.binary(Lt, R2, R3, R2);
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
                        b.load(R3, BSP);
                        b.binary(Ult, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // U>
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Ult, R2, R2, R3);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0
                    build(|b| {
                        b.const_(R2, 0);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // 1
                    build(|b| {
                        b.const_(R2, 1);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // -1
                    build(|b| {
                        b.const_(R2, -1i32 as u32);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // CELL
                    build(|b| {
                        b.const_(R2, CELL);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // -CELL
                    build(|b| {
                        b.const_(R2, (-Wrapping(CELL)).0);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // +
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Add, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // -
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Sub, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // >-<
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Sub, R2, R2, R3);
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
                        b.const_binary(Add, R2, R2, CELL);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // CELL-
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Sub, R2, R2, CELL);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // *
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Mul, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // /
                    build(|b| {
                        b.pop(R2, BSP);
                    }, Ok(State::DivTest)),

                    // MOD
                    build(|b| {
                        b.pop(R2, BSP);
                    }, Ok(State::DivTest)),

                    // /MOD
                    build(|b| {
                        b.pop(R2, BSP);
                    }, Ok(State::DivTest)),

                    // U/MOD
                    build(|b| {
                        b.pop(R2, BSP);
                    }, Ok(State::DivTest)),

                    // S/REM
                    build(|b| {
                        b.pop(R2, BSP);
                    }, Ok(State::DivTest)),

                    // 2/
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Asr, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // CELLS
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Mul, R2, R2, CELL);
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
                        b.load(R3, BSP);
                        b.binary(Max, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // MIN
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Min, R2, R3, R2);
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
                        b.load(R3, BSP);
                        b.binary(And, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // OR
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Or, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // XOR
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Xor, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // LSHIFT
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.const_binary(Ult, BI, R2, CELL_BITS);
                    }, Ok(State::Lshift)),

                    // RSHIFT
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.const_binary(Ult, BI, R2, CELL_BITS);
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
                        b.load(R1, R2);
                        b.binary(Add, R3, R1, R3);
                        b.store(R3, R2);
                    }, Ok(State::Root)),

                    // SP@
                    build(|b| {
                        b.move_(R2, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // SP!
                    build(|b| {
                        b.load(BSP, BSP);
                    }, Ok(State::Root)),

                    // RP@
                    build(|b| {
                        b.push(BRP, BSP);
                    }, Ok(State::Root)),

                    // RP!
                    build(|b| {
                        b.pop(BRP, BSP);
                    }, Ok(State::Root)),

                    // BRANCH
                    build(|_| {}, Ok(State::Branch)),

                    // BRANCHI
                    build(|_| {}, Ok(State::Branchi)),

                    // ?BRANCH
                    build(|b| {
                        b.pop(R2, BSP);
                    }, Ok(State::Qbranch)),

                    // ?BRANCHI
                    build(|b| {
                        b.pop(R2, BSP);
                    }, Ok(State::Qbranchi)),

                    // EXECUTE
                    build(|b| {
                        b.push(BEP, BRP);
                        b.pop(BEP, BSP); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // @EXECUTE
                    build(|b| {
                        b.push(BEP, BRP);
                        b.pop(R2, BSP);
                        b.load(BEP, R2); // FIXME: Add check that EP is valid.
                    }, Ok(State::Next)),

                    // CALL
                    build(|b| {
                        b.const_binary(Add, R1, BEP, CELL);
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
                        b.pop(R2, BSP);
                        b.pop(R3, BSP);
                        // Push two items to RP.
                        b.push(R3, BRP);
                        b.push(R2, BRP);
                    }, Ok(State::Root)),

                    // (LOOP)
                    build(|b| {
                        // Load the index and limit from RP.
                        b.pop(R2, BRP);
                        b.load(R3, BRP);
                        // Update the index.
                        b.const_binary(Add, R2, R2, 1);
                        b.push(R2, BRP);
                        b.binary(Sub, BI, R2, R3);
                    }, Ok(State::Loop)),

                    // (LOOP)I
                    build(|b| {
                        // Load the index and limit from RP.
                        b.pop(R2, BRP);
                        b.load(R3, BRP);
                        // Update the index.
                        b.const_binary(Add, R2, R2, 1);
                        b.push(R2, BRP);
                        b.binary(Sub, BI, R2, R3);
                    }, Ok(State::Loopi)),

                    // (+LOOP)
                    build(|b| {
                        // Pop the step from SP.
                        b.pop(BI, BSP);
                        // Load the index and limit from RP.
                        b.pop(R2, BRP);
                        b.load(R3, BRP);
                        // Update the index.
                        b.binary(Add, R1, R2, BI);
                        b.push(R1, BRP);
                        // Compute the differences between old and new indexes and limit.
                        b.binary(Sub, R2, R2, R3);
                        b.binary(Sub, R3, R1, R3);
                        // Is the step negative?
                        b.const_binary(Lt, BI, BI, 0);
                    }, Ok(State::Ploop)),

                    // (+LOOP)I
                    build(|b| {
                        // Pop the step from SP.
                        b.pop(BI, BSP);
                        // Load the index and limit from RP.
                        b.pop(R2, BRP);
                        b.load(R3, BRP);
                        // Update the index.
                        b.binary(Add, R1, R2, BI);
                        b.push(R1, BRP);
                        // Compute the differences between old and new indexes and limit.
                        b.binary(Sub, R2, R2, R3);
                        b.binary(Sub, R3, R1, R3);
                        // Is the step negative?
                        b.const_binary(Lt, BI, BI, 0);
                    }, Ok(State::Ploopi)),

                    // UNLOOP
                    build(|b| {
                        // Discard two items from RP.
                        b.const_binary(Add, BRP, BRP, 2 * CELL);
                    }, Ok(State::Root)),

                    // J
                    build(|b| {
                        // Push the third item of RP to SP.
                        b.const_binary(Add, R1, BRP, 2 * CELL);
                        b.load(R2, R1);
                        b.push(R2, BSP);
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
                    build(|_| {}, Ok(State::Throw)),

                    // HALT
                    build(|_| {}, Err(Trap::Halt)),

                    // EP@
                    build(|b| {
                        b.push(BEP, BSP);
                    }, Ok(State::Root)),

                    // LIB
                    build(|_| {}, Err(Trap::Lib)),

                    // UNDEFINED
                    build(|_| {}, Err(Trap::Undefined)),

                    // LINK
                    build(|_| {
                        // WONTFIX: no sensible way to call machine code.
                    }, Err(Trap::NotImplemented)),

                    // S0@
                    build(|b| {
                        b.load_register(R2, public_register!(s0));
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // S0!
                    build(|b| {
                        b.pop(R2, BSP);
                        b.store_register(R2, public_register!(s0));
                    }, Ok(State::Root)),

                    // R0@
                    build(|b| {
                        b.load_register(R2, public_register!(r0));
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // R0!
                    build(|b| {
                        b.pop(R2, BSP);
                        b.store_register(R2, public_register!(r0));
                    }, Ok(State::Root)),

                    // 'THROW@
                    build(|b| {
                        b.load_register(R2, public_register!(throw));
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // 'THROW!
                    build(|b| {
                        b.pop(R2, BSP);
                        b.store_register(R2, public_register!(throw));
                    }, Ok(State::Root)),

                    // MEMORY@
                    build(|b| {
                        b.load_register(R2, public_register!(memory));
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // 'BAD@
                    build(|b| {
                        b.load_register(R2, public_register!(bad));
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // -ADDRESS@
                    build(|b| {
                        b.load_register(R2, public_register!(not_address));
                        b.push(R2, BSP);
                    }, Ok(State::Root)),
                ]),
                build(|_| {}, Err(Trap::Undefined)),
            ),
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Root]
    }
}
