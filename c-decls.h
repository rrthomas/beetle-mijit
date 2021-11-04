// C declarations of Rust APIs.
//
// (c) Reuben Thomas 2021
//
// The package is distributed under the GNU Public License version 3, or,
// at your option, any later version.
//
// THIS PROGRAM IS PROVIDED AS IS, WITH NO WARRANTY. USE IS AT THE USER’S
// RISK.

#ifndef MIJIT_BEETLE
#define MIJIT_BEETLE

#include <stdint.h>

typedef struct VM VM;

typedef struct Registers {
    uint32_t ep;
    uint32_t a;
    uint64_t m0;
    uint32_t memory;
    uint32_t sp;
    uint32_t rp;
    uint32_t s0;
    uint32_t r0;
    uint32_t throw;
    uint32_t bad;
    uint32_t not_address;
} Registers;

VM *beetle_new(
    const char * const *argv,
    uint32_t memory_cells, 
    uint32_t data_cells,
    uint32_t return_cells
);


void beetle_drop(VM *vm);

Registers *registers_mut(VM *vm);

int run(VM *vm, uint32_t ep);

#endif
