use clap::{AppSettings, Clap, crate_version, crate_authors};
use mijit::{target::Target};

pub mod vm;
use vm::{VM, BeetleExit, DATA_CELLS, RETURN_CELLS, CELL};

#[derive(Debug)]
enum LoadObjectError {
    BadAddress,
    InvalidFile(&'static str),
}

impl std::error::Error for LoadObjectError {}

impl std::fmt::Display for LoadObjectError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{:?}", self)
    }
}

/**
 * Loads an object file at address 0; on success, returns the next free
 * address.
 */
fn load_object<T: Target>(vm: &mut VM<T>, bytes: &[u8]) -> Result<u32, LoadObjectError> {
    use LoadObjectError::*;
    const MAGIC: &[u8] = b"BEETLE\0";

    struct Reader<'a>(&'a [u8]);
    impl<'a> Reader<'a> {
        fn peek(&self, len: usize) -> Option<&[u8]> {
            if self.0.len() < len {
                None
            } else {
                Some(&self.0[..len])
            }
        }

        fn read(&mut self, len: usize) -> Result<&[u8], LoadObjectError> {
            if self.0.len() < len {
                Err(InvalidFile("unexpected end of file"))
            } else {
                let ret = &self.0[..len];
                self.0 = &self.0[len..];
                Ok(ret)
            }
        }

        fn read_ucell(&mut self, is_be: bool) -> Result<u32, LoadObjectError> {
            let bytes = self.read(4)?;
            let xor_mask = if is_be { 3 } else { 0 };
            let mut ret = 0u32;
            for i in 0..4 {
                ret |= (bytes[i ^ xor_mask] as u32) << (8 * i);
            }
            Ok(ret)
        }
    }

    let mut reader = Reader(bytes);

    // Skip any #! header
    if reader.peek(2) == Some(b"#!") {
        std::mem::drop(reader.read(2));
        while reader.read(1)? != b"\n" {}
    }

    if reader.read(MAGIC.len())? != MAGIC {
        return Err(InvalidFile("bad magic"));
    }

    let endism = reader.read(1)?[0];
    if endism != 0 && endism != 1 {
        return Err(InvalidFile("invalid endism"));
    }
    assert_eq!(endism, 0); // FIXME: Cope with big-endian object files.
    // FIXME: get the actual endism from Mijit.
    let is_be = endism == 1;

    // Find the end of memory.
    let (start, end) = vm.allocate(0);
    assert_eq!(start, end);

    let length = reader.read_ucell(is_be)?;
    let length_bytes = length.checked_mul(CELL).ok_or(BadAddress)?;
    if length_bytes > end {
        return Err(BadAddress);
    }
    for i in 0..length {
        vm.store(i * CELL, reader.read_ucell(is_be)?);
    }

    if reader.peek(1).is_some() {
        return Err(InvalidFile("expected end of file"));
    }

    return Ok(length_bytes);
}

//-----------------------------------------------------------------------------

#[derive(Debug, Clap)]
#[clap(version = crate_version!(), author = crate_authors!())]
#[clap(setting = AppSettings::ColoredHelp)]
struct Opts {
    /** Set memory size to the given NUMBER of cells. 0 < NUMBER <= 1073741824. */
    #[clap(short, long, value_name="NUMBER", default_value="1048576")]
    memory_cells: u32,
    /*
    /** Enter debugger on exception. */
    #[clap(short, long)]
    debug: bool,
    */
    /** Object file to load and run. */
    object_file: String,
    /** Arguments. */
    args: Vec<String>,
}

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let opts: Opts = Opts::parse();
    let mut argv = vec![opts.object_file.clone()];
    argv.extend(opts.args);
    let mut vm = VM::new(
        mijit::target::native(),
        argv.into(),
        opts.memory_cells,
        DATA_CELLS,
        RETURN_CELLS,
    );
    load_object(&mut vm, &std::fs::read(opts.object_file)?)?;
    let (new_vm, exit) = unsafe { vm.run(0) };
    let vm = new_vm;
    match exit {
        BeetleExit::Halt => {
            Ok(())
        },
        BeetleExit::NotImplemented(opcode) => {
            println!("{:#?}", vm);
            panic!("Opcode {:#x} is not implemented", opcode);
        },
        BeetleExit::Undefined(opcode) => {
            println!("{:#?}", vm);
            panic!("Opcode {:#x} is undefined", opcode);
        },
        BeetleExit::InvalidLibRoutine(routine) => {
            println!("{:#?}", vm);
            panic!("LIB routine {:#x} is not implemented", routine);
        },
        BeetleExit::Error(error) => {
            Err(error.into())
        },
    }
}
