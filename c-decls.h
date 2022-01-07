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

typedef struct mijit_beetle_jit mijit_beetle_jit;

typedef struct mijit_beetle_registers {
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
} mijit_beetle_registers;

mijit_beetle_jit *mijit_beetle_new(void);

void mijit_beetle_drop(mijit_beetle_jit *jit);

void mijit_beetle_run(mijit_beetle_jit *jit, uint32_t *m0, mijit_beetle_registers *registers);

#endif
