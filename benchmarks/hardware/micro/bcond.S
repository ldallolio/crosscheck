@ Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
@ Released under the MIT license as described in the file LICENSE.
@ Conditional branches taken and not taken in turn (on the carry of a shift). 50 iterations,
@ 25 on each path.
@ Cycles: movs 2 x 1; even iteration lsrs 1, bcs not taken 1, adds 1, b 3, subs 1, bne 3; odd
@ iteration lsrs 1, bcs taken 3, adds 1, subs 1, bne 3; the last bne 1; bx lr 3.
@ expect cycles: 2 + 25 * 10 + 25 * 9 - 2 + 3
@ expect ret: 75
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
loop:
    lsrs r2, r1, #1
    bcs odd
    adds r0, #2
    b join
odd:
    adds r0, #1
join:
    subs r1, #1
    bne loop
    bx lr
    .size main, .-main
