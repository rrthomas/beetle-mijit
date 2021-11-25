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

typedef struct mijit_beetle_VM mijit_beetle_VM;

typedef struct mijit_beetle_Registers {
    uint32_t ep;
    uint32_t i;
    uint32_t a;
    uint32_t memory;
    uint32_t sp;
    uint32_t rp;
    uint32_t s0;
    uint32_t r0;
    uint32_t throw;
    uint32_t bad;
    uint32_t not_address;
} mijit_beetle_Registers;

mijit_beetle_VM *mijit_beetle_new(
    uint32_t memory_cells, 
    uint32_t data_cells,
    uint32_t return_cells
);


void mijit_beetle_drop(mijit_beetle_VM *vm);

mijit_beetle_Registers *mijit_beetle_registers_mut(mijit_beetle_VM *vm);

uint32_t *mijit_beetle_M0(mijit_beetle_VM *vm);

int mijit_beetle_run(mijit_beetle_VM *vm, uint32_t ep);

#endif
