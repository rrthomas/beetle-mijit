/*!
 * Generate "libmijit_beetle.la" for the benefit of projects that build using
 * libtool.
 */
extern crate libtool;

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() -> std::io::Result<()> {
    let lib = "libmijit_beetle";
    let topdir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let profile = env::var("PROFILE").unwrap();
    let target_dir = format!("{}/target/{}", topdir, profile);
    let libs_dir = format!("{}/.libs", target_dir);
    let new_lib_path = PathBuf::from(format!("{}/{}.a", libs_dir, lib));
    // FIXME: add this to a fork of libtool-rs
    fs::remove_file(new_lib_path)?;
    libtool::generate_convenience_lib(lib).unwrap();
    Ok(())
}