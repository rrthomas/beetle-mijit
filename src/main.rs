use clap::{AppSettings, Clap, crate_version, crate_authors};
use mijit::{target::Target};

mod vm;
pub use vm::{VM, Registers, MEMORY_CELLS, DATA_CELLS, RETURN_CELLS, cell_bytes};

#[derive(Clap)]
#[clap(version = crate_version!(), author = crate_authors!())]
#[clap(setting = AppSettings::ColoredHelp)]
struct Opts {
    /// Object file to load and run.
    object_file: String,
}

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

    let length = reader.read_ucell(is_be)? as i64;
    if cell_bytes(length) > end.into() {
        return Err(BadAddress);
    }
    for i in 0..length {
        vm.store(cell_bytes(i) as u32, reader.read_ucell(is_be)?);
    }

    if reader.peek(1).is_some() {
        return Err(InvalidFile("expected end of file"));
    }

    return Ok(cell_bytes(length) as u32);
}

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let opts: Opts = Opts::parse();

    let mut vm = VM::new(
        mijit::target::native(),
        MEMORY_CELLS,
        DATA_CELLS,
        RETURN_CELLS,
    );
    load_object(&mut vm, &std::fs::read(opts.object_file)?)?;
    unsafe { vm.run(0) };

    Ok(())
}
