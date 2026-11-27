@ Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
@ Released under the MIT license as described in the file LICENSE.
@ Writes of the PC other than branches: MOV PC, rm (to an address made by ADR) and BLX rm
@ (to a function whose address is a literal). 50 iterations.
@ Cycles: push {r4, lr} 3, movs 2 x 1, ldr= 2; per iteration adr 1, mov pc 3, blx 3, leaf (adds 1,
@ bx lr 3), subs 1, bne 3 (1 the last time); pop {r4, pc} 6.
@ expect cycles: 3 + 2 + 2 + 50 * 15 - 2 + 6
@ expect ret: 50
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
    movs r0, #0
    ldr r3, =leaf
loop:
    adr r1, t1
    mov pc, r1
    .balign 4
t1: blx r3
    subs r4, #1
    bne loop
    pop {r4, pc}
    .size main, .-main
    .ltorg
    .balign 4
    .type leaf, %function
    .thumb_func
leaf:
    adds r0, #1
    bx lr
    .size leaf, .-leaf
