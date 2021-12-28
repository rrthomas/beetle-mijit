/** Beetle's registers. */
#[repr(C)]
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
    pub checked: u32,
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

impl Default for Registers {
    fn default() -> Self {
        Registers {
            ep: 0,
            i: 0,
            a: 0,
            memory: 0,
            sp: 0,
            rp: 0,
            s0: 0,
            r0: 0,
            throw: 0,
            bad: 0xFFFFFFFF,
            not_address: 0xFFFFFFFF,
            checked: 0, // Address checking is not implemented.
        }
    }
}
