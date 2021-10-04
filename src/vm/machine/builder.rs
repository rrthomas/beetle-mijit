/*!
 * A utility for generating Mijit code that understands Beetle's conventions.
 */

use mijit::code::{self, Precision, UnaryOp, BinaryOp, Width, Global, IntoVariable, Action, Case};
use Precision::*;
use BinaryOp::*;
use Width::*;
use Action::*;
use super::{CELL, State, Trap, TEMP, M0};

/**
 * Beetle's address space is unified, so we always use the same `AliasMask`.
 */
const AM_MEMORY: code::AliasMask = code::AliasMask(0x1);

/**
 * Beetle's registers are not in Beetle's memory, so we use a different
 * `AliasMask`.
 */
const AM_REGISTER: code::AliasMask = code::AliasMask(0x2);

/**
 * A utility for generating action routines.
 *
 * The methods correspond roughly to the cases of type Action. They fill in
 * Beetle-specific default parameters. `load()` and `store()` add code to map
 * Beetle addresses to native addresses. `push()` and `pop()` access Beetle
 * stacks (the native stack is not used).
 *
 * Example:
 * ```
 * let mut b = Builder::new();
 * b.add_slots(NUM_SLOTS);
 * b.load_register(BEP, public_register!(ep));
 * // ...more code...
 * b.finish()
 * ```
 */
pub struct Builder(Vec<Action>);

impl Builder {
    pub fn new() -> Self {
        Builder(Vec::new())
    }

    pub fn add_slots(&mut self, num_slots: usize) {
        assert_eq!(num_slots & 1, 0);
        for _ in 0..(num_slots >> 1) {
            self.0.push(Push(None, None));
        }
    }

    pub fn remove_slots(&mut self, num_slots: usize) {
        assert_eq!(num_slots & 1, 0);
        self.0.push(DropMany(num_slots >> 1));
    }

    pub fn move_(&mut self, dest: impl IntoVariable, src: impl IntoVariable) {
        if dest.into() != src.into() {
            self.0.push(Move(dest.into(), src.into()));
        }
    }

    pub fn const_(&mut self, dest: impl IntoVariable, constant: u32) {
        self.0.push(Constant(P32, TEMP, constant as i64));
        self.move_(dest, TEMP);
    }

    pub fn const64(&mut self, dest: impl IntoVariable, constant: u64) {
        self.0.push(Constant(P64, TEMP, constant as i64));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 32-bit `op` to `src`, writing `dest`.
     * `TEMP` is corrupted.
     */
    pub fn unary(&mut self, op: UnaryOp, dest: impl IntoVariable, src: impl IntoVariable) {
        self.0.push(Unary(op, P32, TEMP, src.into()));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 32-bit `op` to `src1` and `src2`, writing `dest`.
     * `TEMP` is corrupted.
     */
    pub fn binary(&mut self, op: BinaryOp, dest: impl IntoVariable, src1: impl IntoVariable, src2: impl IntoVariable) {
        self.0.push(Binary(op, P32, TEMP, src1.into(), src2.into()));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 64-bit `op` to `src1` and `src2`, writing `dest`.
     * `TEMP` is corrupted.
     */
    pub fn binary64(&mut self, op: BinaryOp, dest: impl IntoVariable, src1: impl IntoVariable, src2: impl IntoVariable) {
        self.0.push(Binary(op, P64, TEMP, src1.into(), src2.into()));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 32-bit `op` to `src` and `constant`, writing `dest`.
     * `TEMP` is corrupted.
     */
    pub fn const_binary(&mut self, op: BinaryOp, dest: impl IntoVariable, src: impl IntoVariable, constant: u32) {
        assert_ne!(src.into(), TEMP.into());
        self.const_(TEMP, constant);
        self.binary(op, dest, src, TEMP);
    }

    /**
     * Apply 64-bit `op` to `src` and `constant`, writing `dest`.
     * `TEMP` is corrupted.
     */
    pub fn const_binary64(&mut self, op: BinaryOp, dest: impl IntoVariable, src: impl IntoVariable, constant: u64) {
        assert_ne!(src.into(), TEMP.into());
        self.const64(TEMP, constant);
        self.binary64(op, dest, src, TEMP);
    }

    /**
     * Compute the native address corresponding to `addr`.
     * `TEMP` is corrupted.
     */
    pub fn native_address(&mut self, dest: impl IntoVariable, addr: impl IntoVariable) {
        self.binary64(Add, dest, M0, addr);
    }

    /**
     * Compute the native address corresponding to `addr`, and load 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    pub fn load(&mut self, dest: impl IntoVariable, addr: impl IntoVariable) {
        self.native_address(TEMP, addr);
        self.0.push(Load(TEMP, (TEMP.into(), Four), AM_MEMORY));
        self.move_(dest, TEMP);
    }

    /**
     * Compute the native address corresponding to `addr`, and store 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    pub fn store(&mut self, src: impl IntoVariable, addr: impl IntoVariable) {
        assert_ne!(src.into(), TEMP.into());
        self.native_address(TEMP, addr);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Four), AM_MEMORY));
    }

    /**
     * Compute the native address corresponding to `addr`, and load 8 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    pub fn load_byte(&mut self, dest: impl IntoVariable, addr: impl IntoVariable) {
        self.native_address(TEMP, addr);
        self.0.push(Load(TEMP, (TEMP.into(), One), AM_MEMORY));
        self.move_(dest, TEMP);
    }

    /**
     * Compute the native address corresponding to `addr`, and store 8 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    pub fn store_byte(&mut self, src: impl IntoVariable, addr: impl IntoVariable) {
        assert_ne!(src.into(), TEMP.into());
        self.native_address(TEMP, addr);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), One), AM_MEMORY));
    }

    /**
     * Load 32 bits from host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    pub fn load_register(&mut self, dest: impl IntoVariable, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as u64);
        self.0.push(Load(TEMP, (TEMP.into(), Four), AM_REGISTER));
        self.move_(dest, TEMP);
    }

    /**
     * Load 64 bits from host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    pub fn load_register64(&mut self, dest: impl IntoVariable, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as u64);
        self.0.push(Load(TEMP, (TEMP.into(), Eight), AM_REGISTER));
        self.move_(dest, TEMP);
    }

    /**
     * Store 32 bits to host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    pub fn store_register(&mut self, src: impl IntoVariable, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as u64);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Four), AM_REGISTER));
    }

    /**
     * Store 64 bits to host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    pub fn store_register64(&mut self, src: impl IntoVariable, offset: usize) {
        self.const_binary64(Add, TEMP, Global(0), offset as u64);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Eight), AM_REGISTER));
    }

    /**
     * `load()` `dest` from `addr`, then increment `addr`.
     * `TEMP` is corrupted.
     */
    pub fn pop(&mut self, dest: impl IntoVariable, addr: impl IntoVariable) {
        assert_ne!(dest.into(), addr.into());
        assert_ne!(dest.into(), TEMP.into());
        self.load(dest, addr);
        self.const_binary(Add, TEMP, addr, CELL);
        self.move_(addr, TEMP);
    }

    /**
     * Decrement `addr` by `CELL`, then `store()` `src` at `addr`.
     * `TEMP` is corrupted.
     */
    pub fn push(&mut self, src: impl IntoVariable, addr: impl IntoVariable) {
        assert_ne!(src.into(), TEMP.into());
        assert_ne!(src.into(), addr.into());
        self.const_binary(Sub, TEMP, addr, CELL);
        self.move_(addr, TEMP);
        self.store(src, TEMP);
    }

    #[allow(dead_code)]
    pub fn debug(&mut self, x: impl IntoVariable) {
        self.0.push(Debug(x.into()));
    }

    /** Returns all the [`Action`]s that this `Builder` has accumulated. */
    pub fn finish(self) -> Box<[Action]> {
        self.0.into()
    }
}

/**
 * Build a [`Case`], in the form that `Machine::code()` returns.
 *
 * Example:
 * ```
 * Switch::if_(
 *     OPCODE, // `Ult(STACK0, CELL_BITS)`
 *     build(|b| {
 *         b.binary(Lsl, R2, STACK0, STACK1);
 *         b.store(R2, BSP);
 *     }, Ok(State::Root)),
 *     build(|b| {
 *         b.const_(R2, 0);
 *         b.store(R2, BSP);
 *     }, Ok(State::Root)),
 * )
 * ```
 */
pub fn build(
    callback: impl FnOnce(&mut Builder),
    state_or_trap: Result<State, Trap>,
) -> Case<Result<State, Trap>> {
    let mut b = Builder::new();
    callback(&mut b);
    Case {actions: b.0, new_state: state_or_trap}
}

//-----------------------------------------------------------------------------
