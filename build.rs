/*!
 * Generate "libmijit_beetle.la" for the benefit of projects that build using
 * libtool.
 */
extern crate libtool;

fn main() {
    libtool::generate_convenience_lib("libmijit_beetle").unwrap();
}