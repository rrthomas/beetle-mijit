/*! The performance-critical part. */

use std::num::{Wrapping};
use memoffset::{offset_of};
use mijit::code::{UnaryOp, BinaryOp, Width, Global, EBB};
use UnaryOp::*;
use BinaryOp::*;
use mijit::jit::{Jit, EntryId};
use mijit::target::{Target, Word};

#[macro_use]
mod builder;
use builder::{build, marshal, AM_REGISTER};

mod registers;
pub use registers::{Registers};
use registers::map::*;

/** The number of [`Global`]s used by the VM. */
pub const NUM_GLOBALS: usize = 4;

/** The number of bytes in a cell. */
pub const CELL: u32 = 4;

/** The number of bits in a word. */
pub const CELL_BITS: u32 = CELL * 8;

//-----------------------------------------------------------------------------

pub struct VM<T: Target> {
    jit: Option<Jit<T>>,
    root: EntryId,
}

/** Return value that should never happen. */
const UNDEFINED: i64 = -1;

/** Return value for normal exit. */
const NOT_IMPLEMENTED: i64 = 0;

impl<T: Target> VM<T> {
    pub fn new(target: T) -> Self {
        let mut jit = Jit::new(target, NUM_GLOBALS);

        // The main entry point, defined later.
        let root = jit.new_entry(&marshal(vec![BA]), UNDEFINED);

        // The main exit point, used for rare or complex cases.
        let exit = jit.new_entry(&marshal(vec![BA]), NOT_IMPLEMENTED);

        // Merge point for normal exit.
        let not_implemented = jit.new_entry(&marshal(vec![BA, BI]), UNDEFINED);
        jit.define(not_implemented, &build(&|mut b| {
            // Restore the original value of `BA`.
            b.const_binary(Lsl, BA, BA, 8);
            b.b.binary32(Or, BA, BA, BI);
            b.b.jump(exit)
        }));

        // Merge point for throwing exceptions.
        let throw = jit.new_entry(&marshal(vec![]), UNDEFINED);
        jit.define(throw, &build(&|mut b| {
            store_register!(b.b, BEP, bad);
            load_register!(b.b, BEP, throw);
            b.pop(BA, BEP);
            b.b.jump(root)
        }));

        // Merge point for BRANCH.
        let branch = jit.new_entry(&marshal(vec![]), UNDEFINED);
        jit.define(branch, &build(&|mut b| {
            // Load `EP` from the cell it points to.
            b.load(BEP, BEP);
            b.pop(BA, BEP);
            b.b.jump(root)
        }));

        // Merge point for BRANCHI.
        let branchi = jit.new_entry(&marshal(vec![BA]), UNDEFINED);
        jit.define(branchi, &build(&|mut b| {
            // Add `BA` words to `EP`.
            b.const_binary(Mul, R1, BA, CELL);
            b.b.binary32(Add, BEP, BEP, R1);
            b.pop(BA, BEP);
            b.b.jump(root)
        }));

        // An `EBB` for each Beetle op-code.
        let mut dispatch: Box<[EBB<EntryId>]> = (0..0x63).map(|_| {
            build(&|b| { b.b.jump(not_implemented) })
        }).collect();

        // NEXT
        dispatch[0x00] = build(&|mut b| {
            b.pop(BA, BEP);
            b.b.jump(root)
        });

        // DUP
        dispatch[0x01] = build(&|mut b| {
            b.load(R2, BSP);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // DROP
        dispatch[0x02] = build(&|mut b| {
            b.const_binary(Add, BSP, BSP, CELL);
            b.b.jump(root)
        });

        // SWAP
        dispatch[0x03] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.store(R2, BSP);
            b.push(R3, BSP);
            b.b.jump(root)
        });

        // OVER
        dispatch[0x04] = build(&|mut b| {
            b.const_binary(Add, R1, BSP, CELL);
            b.load(R2, R1);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // ROT
        dispatch[0x05] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Add, R1, BSP, CELL);
            b.load(R3, R1);
            b.store(R2, R1);
            b.const_binary(Add, R1, BSP, 2 * CELL);
            b.load(R2, R1);
            b.store(R3, R1);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // -ROT
        dispatch[0x06] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Add, R1, BSP, 2 * CELL);
            b.load(R3, R1);
            b.store(R2, R1);
            b.const_binary(Add, R1, BSP, CELL);
            b.load(R2, R1);
            b.store(R3, R1);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // TUCK
        dispatch[0x07] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Add, R1, BSP, CELL);
            b.load(R3, R1);
            b.store(R2, R1);
            b.store(R3, BSP);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // NIP
        dispatch[0x08] = build(&|mut b| {
            b.pop(R2, BSP);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // TODO: PICK
        // TODO: ROLL

        // ?DUP
        dispatch[0x0B] = build(&|mut b| {
            b.load(R2, BSP);
            b.b.if_(
                R2,
                build(&|mut b| {
                    b.push(R2, BSP);
                    b.b.jump(root)
                }),
                build(&|b| { b.b.jump(root) }),
            )
        });

        // >R
        dispatch[0x0C] = build(&|mut b| {
            b.pop(R2, BSP);
            b.push(R2, BRP);
            b.b.jump(root)
        });

        // R>
        dispatch[0x0D] = build(&|mut b| {
            b.pop(R2, BRP);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // R@
        dispatch[0x0E] = build(&|mut b| {
            b.load(R2, BRP);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // <
        dispatch[0x0F] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Lt, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // >
        dispatch[0x10] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Lt, R2, R2, R3);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // =
        dispatch[0x11] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Eq, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // <>
        dispatch[0x12] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Eq, R2, R3, R2);
            b.b.unary32(Not, R2, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // 0<
        dispatch[0x13] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Lt, R2, R2, 0);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // 0>
        dispatch[0x14] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_(R3, 0);
            b.b.binary32(Lt, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // 0=
        dispatch[0x15] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Eq, R2, R2, 0);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // 0<>
        dispatch[0x16] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Eq, R2, R2, 0);
            b.b.unary32(Not, R2, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // U<
        dispatch[0x17] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Ult, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // U>
        dispatch[0x18] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Ult, R2, R2, R3);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // 0
        dispatch[0x19] = build(&|mut b| {
            b.const_(R2, 0);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // 1
        dispatch[0x1A] = build(&|mut b| {
            b.const_(R2, 1);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // -1
        dispatch[0x1B] = build(&|mut b| {
            b.const_(R2, -1i32 as u32);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // CELL
        dispatch[0x1C] = build(&|mut b| {
            b.const_(R2, CELL);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // -CELL
        dispatch[0x1D] = build(&|mut b| {
            b.const_(R2, (-Wrapping(CELL)).0);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // +
        dispatch[0x1E] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Add, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // -
        dispatch[0x1F] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Sub, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // >-<
        dispatch[0x20] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Sub, R2, R2, R3);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // 1+
        dispatch[0x21] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Add, R2, R2, 1);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // 1-
        dispatch[0x22] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Sub, R2, R2, 1);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // CELL+
        dispatch[0x23] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Add, R2, R2, CELL);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // CELL-
        dispatch[0x24] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Sub, R2, R2, CELL);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // *
        dispatch[0x25] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Mul, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // TODO: /
        // TODO: MOD
        // TODO: /MOD
        // TODO: U/MOD
        // TODO: S/REM

        // 2/
        dispatch[0x2B] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Asr, R2, R2, 1);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // CELLS
        dispatch[0x2C] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Mul, R2, R2, CELL);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // ABS
        dispatch[0x2D] = build(&|mut b| {
            b.load(R2, BSP);
            b.b.unary32(Abs, R2, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // NEGATE
        dispatch[0x2E] = build(&|mut b| {
            b.load(R2, BSP);
            b.b.unary32(Negate, R2, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // MAX
        dispatch[0x2F] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Max, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // MIN
        dispatch[0x30] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Min, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // INVERT
        dispatch[0x31] = build(&|mut b| {
            b.load(R2, BSP);
            b.b.unary32(Not, R2, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // AND
        dispatch[0x32] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(And, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // OR
        dispatch[0x33] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Or, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // XOR
        dispatch[0x34] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.b.binary32(Xor, R2, R3, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // LSHIFT
        dispatch[0x35] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.const_binary(Ult, BI, R2, CELL_BITS);
            b.b.jump(root)
        });

        // RSHIFT
        dispatch[0x36] = build(&|mut b| {
            b.pop(R2, BSP);
            b.load(R3, BSP);
            b.const_binary(Ult, BI, R2, CELL_BITS);
            b.b.jump(root)
        });

        // 1LSHIFT
        dispatch[0x37] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Lsl, R2, R2, 1);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // 1RSHIFT
        dispatch[0x38] = build(&|mut b| {
            b.load(R2, BSP);
            b.const_binary(Lsr, R2, R2, 1);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // @
        dispatch[0x39] = build(&|mut b| {
            b.load(R2, BSP);
            b.load(R2, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // !
        dispatch[0x3A] = build(&|mut b| {
            b.pop(R2, BSP);
            b.pop(R3, BSP);
            b.store(R3, R2);
            b.b.jump(root)
        });

        // C@
        dispatch[0x3B] = build(&|mut b| {
            b.load(R2, BSP);
            b.load_byte(R2, R2);
            b.store(R2, BSP);
            b.b.jump(root)
        });

        // C!
        dispatch[0x3C] = build(&|mut b| {
            b.pop(R2, BSP);
            b.pop(R3, BSP);
            b.store_byte(R3, R2);
            b.b.jump(root)
        });

        // +!
        dispatch[0x3D] = build(&|mut b| {
            b.pop(R2, BSP);
            b.pop(R3, BSP);
            b.load(R1, R2);
            b.b.binary32(Add, R3, R1, R3);
            b.store(R3, R2);
            b.b.jump(root)
        });

        // SP@
        dispatch[0x3E] = build(&|mut b| {
            b.b.move_(R2, BSP);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // SP!
        dispatch[0x3F] = build(&|mut b| {
            b.load(BSP, BSP);
            b.b.jump(root)
        });

        // RP@
        dispatch[0x40] = build(&|mut b| {
            b.push(BRP, BSP);
            b.b.jump(root)
        });

        // RP!
        dispatch[0x41] = build(&|mut b| {
            b.pop(BRP, BSP);
            b.b.jump(root)
        });

        // BRANCH
        dispatch[0x42] = build(&|b| { b.b.jump(branch) });

        // BRANCH
        dispatch[0x43] = build(&|b| { b.b.jump(branchi) });

        // ?BRANCH
        dispatch[0x44] = build(&|mut b| {
            b.pop(R2, BSP);
            b.b.if_(
                R2,
                build(&|mut b| {
                    b.const_binary(Add, BEP, BEP, CELL);
                    b.b.jump(root)
                }),
                build(&|b| { b.b.jump(branch) }),
            )
        });

        // ?BRANCHI
        dispatch[0x45] = build(&|mut b| {
            b.pop(R2, BSP);
            b.b.if_(
                R2,
                build(&|mut b| {
                    b.pop(BA, BEP);
                    b.b.jump(root)
                }),
                build(&|b| { b.b.jump(branchi) }),
            )
        });

        // EXECUTE
        dispatch[0x46] = build(&|mut b| {
            b.push(BEP, BRP);
            b.pop(BEP, BSP);
            b.pop(BA, BEP);
            b.b.jump(root)
        });

        // @EXECUTE
        dispatch[0x47] = build(&|mut b| {
            b.push(BEP, BRP);
            b.pop(R2, BSP);
            b.load(BEP, R2);
            b.pop(BA, BEP);
            b.b.jump(root)
        });

        // CALL
        dispatch[0x48] = build(&|mut b| {
            b.const_binary(Add, R1, BEP, CELL);
            b.push(R1, BRP);
            b.b.jump(branch)
        });

        // CALLI
        dispatch[0x49] = build(&|mut b| {
            b.push(BEP, BRP);
            b.b.jump(branchi)
        });

        // EXIT
        dispatch[0x4A] = build(&|mut b| {
            b.pop(BEP, BRP);
            b.pop(BA, BEP);
            b.b.jump(root)
        });

        // (DO)
        dispatch[0x4B] = build(&|mut b| {
            // Pop two items from SP.
            b.pop(R2, BSP);
            b.pop(R3, BSP);
            // Push two items to RP.
            b.push(R3, BRP);
            b.push(R2, BRP);
            b.b.jump(root)
        });

        // TODO: (LOOP)
        // TODO: (LOOP)I
        // TODO: (+LOOP)
        // TODO: (+LOOP)I

        // UNLOOP
        dispatch[0x50] = build(&|mut b| {
            // Discard two items from RP.
            b.const_binary(Add, BRP, BRP, 2 * CELL);
            b.b.jump(root)
        });

        // J
        dispatch[0x51] = build(&|mut b| {
            // Push the third item of RP to SP.
            b.const_binary(Add, R1, BRP, 2 * CELL);
            b.load(R2, R1);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // (LITERAL)
        dispatch[0x52] = build(&|mut b| {
            // Load R2 from cell pointed to by BEP, and add 4 to EP.
            b.pop(R2, BEP);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // (LITERAL)I
        dispatch[0x53] = build(&|mut b| {
            b.push(BA, BSP);
            b.pop(BA, BEP);
            b.b.jump(root)
        });

        // THROW
        dispatch[0x54] = build(&|b| { b.b.jump(throw) });

        // HALT is left unimplemented.

        // EP@
        dispatch[0x56] = build(&|mut b| {
            b.push(BEP, BSP);
            b.b.jump(root)
        });

        // LIB is left unimplemented.
        // UNDEFINED is left unimplemented.
        // LINK is left unimplemented.

        // S0@
        dispatch[0x5A] = build(&|mut b| {
            load_register!(b.b, R2, s0);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // S0!
        dispatch[0x5B] = build(&|mut b| {
            b.pop(R2, BSP);
            store_register!(b.b, R2, s0);
            b.b.jump(root)
        });

        // R0@
        dispatch[0x5C] = build(&|mut b| {
            load_register!(b.b, R2, r0);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // R0!
        dispatch[0x5D] = build(&|mut b| {
            b.pop(R2, BSP);
            store_register!(b.b, R2, r0);
            b.b.jump(root)
        });

        // 'THROW@
        dispatch[0x5E] = build(&|mut b| {
            load_register!(b.b, R2, throw);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // 'THROW!
        dispatch[0x5F] = build(&|mut b| {
            b.pop(R2, BSP);
            store_register!(b.b, R2, throw);
            b.b.jump(root)
        });

        // MEMORY@
        dispatch[0x60] = build(&|mut b| {
            load_register!(b.b, R2, memory);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // 'BAD@
        dispatch[0x61] = build(&|mut b| {
            load_register!(b.b, R2, bad);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // -ADDRESS@
        dispatch[0x62] = build(&|mut b| {
            load_register!(b.b, R2, not_address);
            b.push(R2, BSP);
            b.b.jump(root)
        });

        // Define the main entry point.
        jit.define(root, &build(&move |mut b| {
            b.const_binary(And, BI, BA, 0xFF);
            b.const_binary(Asr, BA, BA, 8);
            b.b.index(
                BI,
                dispatch.clone(),
                build(&|b| { b.b.jump(not_implemented) }),
            )
        }));
        VM {jit: Some(jit), root: root}
    }

    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        self.jit.as_mut().expect("Poisoned").global_mut(global)
    }

    /// # Safety
    ///
    /// Beetle programs can corrupt arbitrary memory, as bounds checking is not
    /// implemented.
    pub unsafe fn run(&mut self) {
        let inner: Jit<T> = self.jit.take().expect("Poisoned");
        let (inner, result) = inner.run(self.root).expect("Execute failed");
        assert_eq!(result, Word {s: NOT_IMPLEMENTED});
        self.jit = Some(inner);
    }
}