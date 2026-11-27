@ Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
@ Released under the MIT license as described in the file LICENSE.
@ Calls (BL) of a function that saves and restores five registers (PUSH, POP {..., pc}).
@ 50 iterations.
@ Cycles: push {r4, lr} 3, movs 1; per iteration bl 4, leaf (push 6, movs 1, pop {r4-r7, pc} 9),
@ subs 1, bne 3 (1 the last time); pop {r4, pc} 6.
@ expect cycles: 3 + 1 + 50 * 24 - 2 + 6
@ expect ret: 7
    .syntax unified
    .cpu cortex-m0
    .thumb
    .text
    .balign 4
    .global main
    .type main, %function
    .thumb_func
main:
    push {r4, lr}
    movs r4, #50
loop:
    bl leaf
    subs r4, #1
    bne loop
    pop {r4, pc}
    .balign 4
    .type leaf, %function
    .thumb_func
    .size main, .-main
leaf:
    push {r4-r7, lr}
    movs r0, #7
    pop {r4-r7, pc}
    .size leaf, .-leaf
