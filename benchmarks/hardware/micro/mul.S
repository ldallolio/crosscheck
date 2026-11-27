@ Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
@ Released under the MIT license as described in the file LICENSE.
@ MULS, 8 per iteration, 50 iterations: decides the multiplier of the core (1 cycle or 32).
@ Cycles: movs 3 x 1; per iteration 8 x m + subs 1 + bne 3 (1 the last time); bx lr 3.
@ expect cycles: 3 + 50 * (8 * m + 4) - 2 + 3
@ expect ret: 3 ** 400 % 2 ** 32
    .syntax unified
    .cpu cortex-m0
    .thumb
    .text
    .balign 4
    .global main
    .type main, %function
    .thumb_func
main:
    movs r0, #1
    movs r1, #3
    movs r2, #50
loop:
    muls r0, r1, r0
    muls r0, r1, r0
    muls r0, r1, r0
    muls r0, r1, r0
    muls r0, r1, r0
    muls r0, r1, r0
    muls r0, r1, r0
    muls r0, r1, r0
    subs r2, #1
    bne loop
    bx lr
    .size main, .-main
