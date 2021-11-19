# Makefile.am for mijit-beetle
#
# Copyright (C) Reuben Thomas 2021

ACLOCAL_AMFLAGS = -I m4

lib_LTLIBRARIES = target/release/libmijit_beetle.la

target/release/libmijit_beetle.la:
	cargo build --release --manifest-path $(srcdir)/Cargo.toml
