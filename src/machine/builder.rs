//! A utility for generating Mijit code that understands Beetle's conventions.

use memoffset::{offset_of};
use mijit::code::{BinaryOp, Width, AliasMask, Register, Global, Variable, EBB, Marshal};
use BinaryOp::{Add, Sub};
use super::super::mijit_builder::{self, TEMP};

use super::{CELL};

/**
 * Beetle's address space is unified, so we always use the same `AliasMask`.
 */
pub const AM_MEMORY: AliasMask = AliasMask(0x1);

/**
 * Beetle's registers are not in Beetle's memory, so we use a different
 * `AliasMask`.
 */
pub const AM_REGISTER: AliasMask = AliasMask(0x2);

//-----------------------------------------------------------------------------

pub fn build<T>(callback: &dyn Fn(Builder<T>) -> EBB<T>) -> EBB<T> {
    mijit_builder::build(&|b| callback(Builder {b}))
}

//-----------------------------------------------------------------------------

pub struct Builder<T> {
    pub b: mijit_builder::Builder<T>
}

impl<T> Builder<T> {
    pub fn const_(&mut self, dest: Register, constant: u32) {
        self.b.const_(dest, constant as i64);
    }

    /**
     * Apply 32-bit `op` to `src` and `constant`, writing `dest`.
     * `TEMP` is corrupted.
     */
    pub fn const_binary(&mut self, op: BinaryOp, dest: Register, src: Register, constant: u32) {
        assert_ne!(src, TEMP);
        self.const_(TEMP, constant);
        self.b.binary32(op, dest, src, TEMP);
    }

    /** Compute the native address corresponding to `addr`. */
    pub fn native_address(&mut self, dest: Register, addr: Register) {
        self.b.binary64(Add, dest, M0, addr);
    }

    /**
     * Compute the native address corresponding to `addr`, and load 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    pub fn load(&mut self, dest: Register, addr: Register) {
        self.native_address(TEMP, addr);
        self.b.load(dest, (TEMP, 0), Width::Four, AM_MEMORY);
    }

    /**
     * Compute the native address corresponding to `addr`, and store 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    pub fn store(&mut self, src: Register, addr: Register) {
        assert_ne!(src, TEMP);
        self.native_address(TEMP, addr);
        self.b.store(TEMP, (TEMP, 0), Width::Four, AM_MEMORY);
    }

    /**
     * Compute the native address corresponding to `addr`, and load 8 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    pub fn load_byte(&mut self, dest: Register, addr: Register) {
        self.native_address(TEMP, addr);
        self.b.load(dest, (TEMP, 0), Width::One, AM_MEMORY);
    }

    /**
     * Compute the native address corresponding to `addr`, and store 8 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    pub fn store_byte(&mut self, src: Register, addr: Register) {
        assert_ne!(src, TEMP);
        self.native_address(TEMP, addr);
        self.b.store(TEMP, (TEMP, 0), Width::One, AM_MEMORY);
    }

    /**
     * `load()` `dest` from `addr`, then increment `addr`.
     * `TEMP` is corrupted.
     */
    pub fn pop(&mut self, dest: Register, addr: Register) {
        assert_ne!(dest, addr);
        assert_ne!(dest, TEMP);
        self.load(dest, addr);
        self.const_binary(Add, addr, addr, CELL);
    }

    /**
     * Decrement `addr` by `CELL`, then `store()` `src` at `addr`.
     * `TEMP` is corrupted.
     */
    pub fn push(&mut self, src: Register, addr: Register) {
        assert_ne!(src, TEMP);
        assert_ne!(src, addr);
        self.const_binary(Sub, addr, addr, CELL);
        self.store(src, addr);
    }
}

//-----------------------------------------------------------------------------

use super::{Registers};
use super::registers::map::*;

macro_rules! load_register {
    ($b: expr, $dest: expr, $field: ident) => {
        $b.load($dest, (Global(0), offset_of!(Registers, $field) as i64), Width::Four, AM_REGISTER);
    }
}

macro_rules! store_register {
    ($b: expr, $src: expr, $field: ident) => {
        $b.store($src, (Global(0), offset_of!(Registers, $field) as i64), Width::Four, AM_REGISTER);
    }
}

/**
 * Construct a [`Marshal`] with live values [`Global(0)`], [`BEP`], [`BSP`],
 * [`BRP`], [`M0`], and `extra_live_registers`.
 */
pub fn marshal(extra_live_registers: Vec<Register>) -> Marshal {
    let mut live_values = vec![Global(0).into(), BEP.into(), BSP.into(), BRP.into(), M0.into()];
    live_values.extend(extra_live_registers.into_iter().map(Variable::Register));
    let prologue = mijit_builder::build_block(&|b| {
        load_register!(b, BEP, ep);
        load_register!(b, BI, i);
        load_register!(b, BA, a);
        load_register!(b, BSP, sp);
        load_register!(b, BRP, rp);
        b.move_(M0, Global(1));
        b.move_(R2, Global(2));
        b.move_(R3, Global(3));
    });
    let epilogue = mijit_builder::build_block(&|b| {
        for v in [BA, BI, R2, R3] {
            if !live_values.contains(&Variable::Register(v)) {
                b.const_(v, 0xDEADDEADDEADDEADu64 as i64);
            }
        }
        store_register!(b, BEP, ep);
        store_register!(b, BI, i);
        store_register!(b, BA, a);
        store_register!(b, BSP, sp);
        store_register!(b, BRP, rp);
        b.move_(Global(1), M0);
        b.move_(Global(2), R2);
        b.move_(Global(3), R3);
    });
    Marshal {prologue, epilogue}
}
