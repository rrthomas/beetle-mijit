mod vm;
pub use vm::{VM, Registers, MEMORY_CELLS, DATA_CELLS, RETURN_CELLS};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("Hello, world!");
    Ok(())
}
