@ Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
@ Released under the MIT license as described in the file LICENSE.
@ Taken branches to targets at addresses 0 and 2 modulo 4 (the core fetches 32-bit words).
@ 50 iterations.
@ Cycles: movs 2 x 1; per iteration adds 4 x 1 + b 3 x 3 + subs 1 + bne 3 (1 the last time);
@ bx lr 3.
@ expect cycles: 2 + 50 * 17 - 2 + 3
@ expect ret: 200
    .syntax unified
    .cpu cortex-m0
    .thumb
    .text
    .balign 4
    .global main
    .type main, %function
    .thumb_func
main:
    movs r0, #0
    movs r1, #50
loop:                   @ main + 4: 0 mod 4
    adds r0, #1
    b t1
    nop                 @ not executed
t1: adds r0, #1         @ 2 mod 4
    b t2
t2: adds r0, #1         @ 2 mod 4, the next instruction
    b t3
    nop                 @ not executed
t3: adds r0, #1         @ 0 mod 4
    subs r1, #1
    bne loop
    bx lr
    .size main, .-main
