use std::convert::{TryFrom};
use mijit::target::{Target, Word};
use mijit::{jit};
use mijit::code::{Global};

/** Beetle's registers that are live in [`State::Root`]. */
#[repr(C)]
#[derive(Default)]
pub struct Registers {
    pub ep: u32,
    pub a: u32,
    pub sp: u32,
    pub rp: u32,
    pub s0: u32,
    pub r0: u32,
    pub throw: u32,
    pub bad: u32,
    pub not_address: u32,
}

/** Beetle's registers, including those live in all [`State`]s. */
#[repr(C)]
#[derive(Default)]
struct AllRegisters {
    public: Registers,
    memory: u64,
    opcode: u32,
    stack0: u32,
    stack1: u32,
    loop_new: u32,
    loop_old: u32,
}

//-----------------------------------------------------------------------------

/** Computes the number of bytes in `n` cells. */
pub const fn cell_bytes(n: i64) -> i64 { 4 * n }

mod machine;
pub use machine::{Machine};
use machine::{State, Trap};

//-----------------------------------------------------------------------------

/** The suggested size of the Beetle memory, in cells. */
pub const MEMORY_CELLS: u32 = 1 << 20;
/** The suggested size of the Beetle data stack, in cells. */
pub const DATA_CELLS: u32 = 1 << 18;
/** The suggested size of the Beetle return stack, in cells. */
pub const RETURN_CELLS: u32 = 1 << 18;

pub struct VM<T: Target> {
    /** The compiled code, registers, and other compiler state. */
    jit: jit::Jit<Machine, T>,
    /** The Beetle state (other than the memory). */
    state: AllRegisters,
    /** The Beetle memory. */
    memory: Vec<u32>,
    /** The amount of unallocated memory, in cells. */
    free_cells: u32,
    /** The address of a HALT instruction. */
    halt_addr: u32,
}

impl<T: Target> VM<T> {
    /**
     * Constructs a Beetle virtual machine with the specified parameters.
     *
     * The memory is `memory_cells` cells. The data stack occupies the last
     * `data_cells` cells of the memory, and the return stack occupies
     * the last `return_cells` cells before that. The cells before that
     * are free for the program's use.
     */
    pub fn new(
        target: T,
        memory_cells: u32,
        data_cells: u32,
        return_cells: u32,
    ) -> Self {
        let mut vm = VM {
            jit: jit::Jit::new(&Machine, target),
            state: AllRegisters::default(),
            memory: vec![0; memory_cells as usize],
            free_cells: memory_cells,
            halt_addr: 0,
        };
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
        vm.store(vm.halt_addr, 0x5F);
        vm
    }

    /** Read the public registers. */
    pub fn registers(&self) -> &Registers { &self.state.public }

    /** Read or write the public registers. */
    pub fn registers_mut(&mut self) -> &mut Registers { &mut self.state.public }

    /**
     * Allocate `cells` cells and return a (start, end) Beetle pointer pair.
     * Allocation starts at the top of memory and is permanent.
     */
    pub fn allocate(&mut self, cells: u32) -> (u32, u32) {
        assert!(cells <= self.free_cells);
        let end = u32::try_from(
            cell_bytes(i64::from(self.free_cells))
        ).expect("Address out of range");
        self.free_cells -= cells;
        let start = u32::try_from(
            cell_bytes(i64::from(self.free_cells))
        ).expect("Address out of range");
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

    /** Push `item` onto the data stack. */
    pub fn push(&mut self, item: u32) {
        self.registers_mut().sp -= cell_bytes(1) as u32;
        self.store(self.registers().sp, item);
    }

    /** Pop an item from the data stack. */
    pub fn pop(&mut self) -> u32 {
        let item = self.load(self.registers().sp);
        self.registers_mut().sp += cell_bytes(1) as u32;
        item
    }

    /** Push `item` onto the return stack. */
    pub fn rpush(&mut self, item: u32) {
        self.registers_mut().rp -= cell_bytes(1) as u32;
        self.store(self.registers().rp, item);
    }

    /** Pop an item from the return stack. */
    pub fn rpop(&mut self) -> u32 {
        let item = self.load(self.registers().rp);
        self.registers_mut().rp += cell_bytes(1) as u32;
        item
    }

    /**
     * Run the code at address `ep`.
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`].
     */
    pub unsafe fn run(mut self, ep: u32) -> Self {
        assert!(Self::is_aligned(ep));
        self.registers_mut().ep = ep;
        self.state.memory = self.memory.as_mut_ptr() as u64;
        *self.jit.global_mut(Global(0)) = Word {mp: (&mut self.state as *mut AllRegisters).cast()};
        let (jit, trap) = self.jit.execute(&State::Root).expect("Execute failed");
        assert_eq!(trap, Trap::Halt);
        self.jit = jit;
        self
    }

    /** Indicate whether an address is cell-aligned. */
    pub fn is_aligned(addr: u32) -> bool {
        addr & 0x3 == 0
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    use mijit::target::{native};

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
            0x00001504, 0x0000024F, 0x00002108, 0x0000084D,
            0x00001501, 0x0000034F, 0x001A2202, 0xFFFFF853,
            0x0000034D, 0x22062204, 0xFFFFF553, 0xFFFFF453,
            0x00000054,
        ]
    }

    #[test]
    pub fn halt() {
        let mut vm = VM::new(native(), MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        let entry_address = vm.halt_addr;
        vm = unsafe { vm.run(entry_address) };
        assert_eq!(vm.registers().s0, vm.registers().sp);
        assert_eq!(vm.registers().r0, vm.registers().rp);
    }

    #[test]
    pub fn ackermann() {
        let mut vm = VM::new(native(), MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        vm.load_object(ackermann_object().as_ref());
        vm.push(3);
        vm.push(5);
        vm.rpush(vm.halt_addr);
        vm = unsafe { vm.run(0) };
        let result = vm.pop();
        assert_eq!(vm.registers().s0, vm.registers().sp);
        assert_eq!(vm.registers().r0, vm.registers().rp);
        assert_eq!(result, 253);
    }

    // TODO: Test (LOOP) instructions.
}
