use mijit::target::{Native, native, Word};
use mijit::{jit};
use mijit::code::{Global};

/** Beetle's registers. */
#[repr(C)]
#[derive(Default)]
pub struct Registers {
    pub ep: u32,
    pub i: u32,
    pub a: u32,
    pub memory: u32,
    pub sp: u32,
    pub rp: u32,
    pub s0: u32,
    pub r0: u32,
    pub throw: u32,
    pub bad: u32,
    pub not_address: u32,
}

impl std::fmt::Debug for Registers {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        f.debug_struct("Registers")
            .field("ep", &format!("{:#x}", self.ep))
            .field("i", &format!("{:#x}", self.i))
            .field("a", &format!("{:#x}", self.a))
            .field("memory", &format!("{:#x}", self.memory))
            .field("sp", &format!("{:#x}", self.sp))
            .field("rp", &format!("{:#x}", self.rp))
            .field("s0", &format!("{:#x}", self.s0))
            .field("r0", &format!("{:#x}", self.r0))
            .field("throw", &format!("{:#x}", self.throw))
            .field("bad", &format!("{:#x}", self.bad))
            .field("not_address", &format!("{:#x}", self.not_address))
            .finish()
    }
}

/**
 * Beetle's registers, including those live in all [`State`]s.
 *
 * [State]: mijit::code::Machine::State
 */
#[repr(C)]
#[derive(Default)]
struct AllRegisters {
    public: Registers,
    m0: u64,
    r2: u32,
    r3: u32,
}

impl std::fmt::Debug for AllRegisters {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        f.debug_struct("AllRegisters")
            .field("public", &self.public)
            .field("m0", &format!("{:#x}", self.m0))
            .field("r2", &format!("{:#x}", self.r2))
            .field("r3", &format!("{:#x}", self.r3))
            .finish()
    }
}

//-----------------------------------------------------------------------------

mod machine;
pub use machine::{CELL, Machine};
use machine::{State, Trap};

//-----------------------------------------------------------------------------

/** The return type of `VM::run()`. */
#[derive(Debug)]
pub enum BeetleExit {
    Halt(u32),
    NotImplemented(u8),
    Undefined(u8),
    Lib,
}

//-----------------------------------------------------------------------------

/** The suggested size of the Beetle memory, in cells. */
pub const MEMORY_CELLS: u32 = 1 << 20;
/** The suggested size of the Beetle data stack, in cells. */
pub const DATA_CELLS: u32 = 1 << 18;
/** The suggested size of the Beetle return stack, in cells. */
pub const RETURN_CELLS: u32 = 1 << 18;

/** The type of VM::jit. */
type Jit = jit::Jit<Machine, Native>;

pub struct VM {
    /** The compiled code, registers, and other compiler state. */
    jit: Option<Jit>,
    /** The Beetle state (other than the memory). */
    state: AllRegisters,
    /** The Beetle memory. */
    memory: Vec<u32>,
    /** The amount of unallocated memory, in cells. */
    free_cells: u32,
    /** The address of a HALT instruction. */
    halt_addr: u32,
}

impl VM {
    /**
     * Constructs a Beetle virtual machine with the specified parameters.
     *
     * The memory is `memory_cells` cells. The data stack occupies the last
     * `data_cells` cells of the memory, and the return stack occupies
     * the last `return_cells` cells before that. The cells before that
     * are free for the program's use.
     */
    pub fn new(
        memory_cells: u32,
        data_cells: u32,
        return_cells: u32,
    ) -> Self {
        let mut vm = VM {
            jit: Some(jit::Jit::new(&Machine, native())),
            state: AllRegisters::default(),
            memory: vec![0; memory_cells as usize],
            free_cells: memory_cells,
            halt_addr: 0,
        };
        // Set memory size register.
        vm.registers_mut().memory = memory_cells.checked_mul(CELL)
            .expect("Address out of range");
        // Allocate the data stack.
        let sp = vm.allocate(data_cells).1;
        vm.registers_mut().s0 = sp;
        vm.registers_mut().sp = sp;
        // Allocate the return stack.
        let rp = vm.allocate(return_cells).1;
        vm.registers_mut().r0 = rp;
        vm.registers_mut().rp = rp;
        // Allocate a word to hold a HALT instruction.
        vm.halt_addr = vm.allocate(1).0;
        vm.store(vm.halt_addr, 0x5519);
        vm
    }

    /** Read the public registers. */
    pub fn registers(&self) -> &Registers { &self.state.public }

    /** Read or write the public registers. */
    pub fn registers_mut(&mut self) -> &mut Registers { &mut self.state.public }

    /** Read the `M0` register. */
    pub fn memory(&self) -> &[u32] { &self.memory }

    /**
     * Allocate `cells` cells and return a (start, end) Beetle pointer pair.
     * Allocation starts at the top of memory and is permanent.
     */
    pub fn allocate(&mut self, cells: u32) -> (u32, u32) {
        assert!(cells <= self.free_cells);
        let end = self.free_cells.checked_mul(CELL)
            .expect("Address out of range");
        self.free_cells = self.free_cells.checked_sub(cells)
            .expect("Out of memory");
        let start = self.free_cells.checked_mul(CELL)
            .expect("Address out of range");
        (start, end)
    }

    /**
     * Load `object` at address zero, i.e. in the unallocated memory.
     */
    pub fn load_object(&mut self, object: &[u32]) {
        assert!(object.len() <= self.free_cells as usize);
        for (i, &cell) in object.iter().enumerate() {
            self.memory[i] = cell;
        }
    }

    /** Return the value of the word at address `addr`. */
    pub fn load(&self, addr: u32) -> u32 {
        assert_eq!(addr & 0x3, 0);
        self.memory[(addr >> 2) as usize]
    }

    /** Set the word at address `addr` to `value`. */
    pub fn store(&mut self, addr: u32, value: u32) {
        assert_eq!(addr & 0x3, 0);
        self.memory[(addr >> 2) as usize] = value;
    }

    /** Return the value of the byte at address `addr`. */
    pub fn load_byte(&self, addr: u32) -> u8 {
        let word = self.memory[(addr >> 2) as usize];
        let which_byte = (addr & 3) as usize;
        (word >> (8 * which_byte)) as u8
    }

    /** Set the byte at address `addr` to `value`. */
    pub fn store_byte(&mut self, addr: u32, value: u8) {
        let word = self.memory[(addr >> 2) as usize];
        let which_byte = (addr & 3) as usize;
        let byte_mask = 0xFFu32 << (8 * which_byte);
        let new_word = (word & !byte_mask) | ((value as u32) << (8 * which_byte));
        self.memory[(addr >> 2) as usize] = new_word;
    }

    /** Returns a copy of `len` bytes starting at `addr`. */
    pub fn get_str(&self, addr: u32, len: u32) -> Vec<u8> {
        (0..len).map(|i| self.load_byte(addr + i)).collect()
    }

    /** Push `item` onto the data stack. */
    pub fn push(&mut self, item: u32) {
        self.registers_mut().sp -= CELL;
        self.store(self.registers().sp, item);
    }

    /** Pop an item from the data stack. */
    pub fn pop(&mut self) -> u32 {
        let item = self.load(self.registers().sp);
        self.registers_mut().sp += CELL;
        item
    }

    /** Push the low and high words of `item` onto the data stack. */
    pub fn push_double(&mut self, item: u64) {
        self.push(item as u32);
        self.push((item >> 32) as u32);
    }

    /** Pop the high and low words of an item from the data stack. */
    pub fn pop_double(&mut self) -> u64 {
        let high = self.pop() as u64;
        let low = self.pop() as u64;
        low | (high << 32)
    }

    /** Push `item` onto the return stack. */
    pub fn rpush(&mut self, item: u32) {
        self.registers_mut().rp -= CELL;
        self.store(self.registers().rp, item);
    }

    /** Pop an item from the return stack. */
    pub fn rpop(&mut self) -> u32 {
        let item = self.load(self.registers().rp);
        self.registers_mut().rp += CELL;
        item
    }

    /** Run the code at address `ep`. */
    pub fn run(&mut self, ep: u32) -> BeetleExit {
        assert!(Self::is_aligned(ep));
        self.registers_mut().ep = ep;
        self.state.m0 = self.memory.as_mut_ptr() as u64;
        let mut jit = self.jit.take().expect("Trying to call run() after error");
        *jit.global_mut(Global(0)) = Word {mp: (&mut self.state as *mut AllRegisters).cast()};
        let (jit, trap) = unsafe {jit.execute(&State::Root)}.expect("Execute failed");
        self.jit = Some(jit);
        let opcode = self.registers_mut().i as u8;
        match trap {
            Trap::Halt => BeetleExit::Halt(self.pop()),
            Trap::NotImplemented => BeetleExit::NotImplemented(opcode as u8),
            Trap::Lib => BeetleExit::Lib,
            Trap::Undefined => BeetleExit::Undefined(opcode as u8),
        }
    }

    /** Indicate whether an address is cell-aligned. */
    pub fn is_aligned(addr: u32) -> bool {
        addr & 0x3 == 0
    }
}

impl std::fmt::Debug for VM {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.state.fmt(f)
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    pub const TEST_VALUES: [u32; 10] = [
        0x00000000,
        0x00000001,
        0x11111111,
        0x01234567,
        0x7FFFFFFF,
        0x80000000,
        0xEEEEEEEE,
        0xFEDCBA98,
        0xFFFFFFFE,
        0xFFFFFFFF,
    ];

    pub fn ackermann_object() -> Vec<u32> {
        // Forth source:
        // : ACKERMANN   ( m n -- result )
        // OVER 0= IF                  \ m = 0
        //     NIP 1+                  \ n+1
        // ELSE
        //     DUP 0= IF               \ n = 0
        //         DROP 1- 1 RECURSE   \ A(m-1, 1)
        //     ELSE
        //         OVER 1- -ROT        \ m-1 m n
        //         1- RECURSE          \ m-1 A(m, n-1)
        //         RECURSE             \ A(m-1, A(m, n-1))
        //     THEN
        // THEN ;

        // Beetle assembler:
        // $00: OVER
        //      0=
        // $04: ?BRANCHI $10
        // $08: NIP
        //      1+
        // $0C: BRANCHI $30
        // $10: DUP
        //      0=
        // $14: ?BRANCHI $24
        // $18: DROP
        //      1-
        //      1
        // $1C: CALLI $0
        // $20: BRANCHI $30
        // $24: OVER
        //      1-
        //      -ROT
        //      1-
        // $28: CALLI $0
        // $2C: CALLI $0
        // $30: EXIT

        // Beetle object code:
        vec![
            0x00001504, 0x00000245, 0x00002108, 0x00000843,
            0x00001501, 0x00000345, 0x001A2202, 0xFFFFF849,
            0x00000343, 0x22062204, 0xFFFFF549, 0xFFFFF449,
            0x0000004A,
        ]
    }

    #[test]
    pub fn halt() {
        let mut vm = VM::new(MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        let entry_address = vm.halt_addr;
        let exit = vm.run(entry_address);
        assert!(matches!(exit, BeetleExit::Halt(0)));
        assert_eq!(vm.registers().s0, vm.registers().sp);
        assert_eq!(vm.registers().r0, vm.registers().rp);
    }

    #[test]
    pub fn ackermann() {
        let mut vm = VM::new(MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        vm.load_object(ackermann_object().as_ref());
        vm.push(3);
        vm.push(5);
        vm.rpush(vm.halt_addr);
        let exit = vm.run(0);
        assert!(matches!(exit, BeetleExit::Halt(0)));
        let result = vm.pop();
        assert_eq!(vm.registers().s0, vm.registers().sp);
        assert_eq!(vm.registers().r0, vm.registers().rp);
        assert_eq!(result, 253);
    }

    // Test arithmetic instructions.

    fn test_unary(
        opcode: u8,
        expected: fn(u32) -> u32,
    ) {
        let mut vm = VM::new(MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        vm.registers_mut().throw = vm.halt_addr;
        vm.store(0, 0x551900 | (opcode as u32));
        for x in TEST_VALUES {
            println!("Operating on {:x}", x);
            vm.push(x);
            let exit = vm.run(0);
            assert!(matches!(exit, BeetleExit::Halt(0)));
            let observed = vm.pop();
            assert_eq!(observed, expected(x));
            assert_eq!(vm.registers().s0, vm.registers().sp);
            assert_eq!(vm.registers().r0, vm.registers().rp);
        }
    }

    #[test]
    fn one_lshift() {
        test_unary(0x37, |x| x << 1);
    }

    // Test division instructions.

    /** Slow but correct division rounding quotient down. */
    fn floor_div_mod(numerator: i32, denominator: i32) -> (i32, i32) {
        let quotient = ((numerator as f64) / (denominator as f64)).floor() as i64 as i32;
        let remainder = numerator.wrapping_sub(quotient.wrapping_mul(denominator));
        (quotient, remainder)
    }

    /** Slow but correct division rounding quotient towards zero. */
    fn trunc_div_mod(numerator: i32, denominator: i32) -> (i32, i32) {
        let quotient = ((numerator as f64) / (denominator as f64)).trunc() as i64 as i32;
        let remainder = numerator.wrapping_sub(quotient.wrapping_mul(denominator));
        (quotient, remainder)
    }

    /** Applies `opcode` to various inputs and checks the resulting stack. */
    fn test_div(
        opcode: u8,
        expected: fn(u32, u32) -> Vec<u32>,
    ) {
        let mut vm = VM::new(MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        vm.registers_mut().throw = vm.halt_addr;
        vm.store(0, 0x551900 | (opcode as u32));
        for x in TEST_VALUES {
            for y in TEST_VALUES {
                println!("Dividing {:x} by {:x}", x, y);
                vm.push(x);
                vm.push(y);
                let exit = vm.run(0);
                assert!(matches!(exit, BeetleExit::Halt(0)));
                if y != 0 {
                    // Division should work.
                    for z in expected(x, y) {
                        let observed = vm.pop();
                        assert_eq!(observed, z);
                    }
                    assert_eq!(vm.registers().s0, vm.registers().sp);
                    assert_eq!(vm.registers().r0, vm.registers().rp);
                } else {
                    // Division should throw.
                    let exception = vm.pop();
                    assert_eq!(vm.registers().s0, vm.registers().sp);
                    assert_eq!(vm.registers().r0, vm.registers().rp);
                    assert_eq!(exception, -10i32 as u32);
                }
            }
        }
    }

    #[test]
    pub fn slash() {
        test_div(0x26, |x, y| {
            let (q, _) = floor_div_mod(x as i32, y as i32);
            vec![q as u32]
        });
    }

    #[test]
    pub fn mod_() {
        test_div(0x27, |x, y| {
            let (_, r) = floor_div_mod(x as i32, y as i32);
            vec![r as u32]
        });
    }

    #[test]
    pub fn slash_mod() {
        test_div(0x28, |x, y| {
            let (q, r) = floor_div_mod(x as i32, y as i32);
            vec![q as u32, r as u32]
        });
    }

    #[test]
    pub fn u_slash_mod() {
        test_div(0x29, |x, y| {
            vec![x / y, x % y]
        });
    }

    #[test]
    pub fn s_slash_rem() {
        test_div(0x2A, |x, y| {
            let (q, r) = trunc_div_mod(x as i32, y as i32);
            vec![q as u32, r as u32]
        });
    }

    // TODO: Test (LOOP) instructions.
}
