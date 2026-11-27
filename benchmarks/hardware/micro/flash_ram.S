@ Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
@ Released under the MIT license as described in the file LICENSE.
@ Loads from the flash (a constant table) and loads and stores in RAM, words, bytes and
@ halfwords. 50 iterations.
@ Cycles: push {r4, lr} 3, ldr= 2 x 2, movs 2 x 1; per iteration ldr 2, str 2, ldr 2, adds 1,
@ ldrb 2, ldrh 2, subs 1, bne 3 (1 the last time); pop {r4, pc} 6.
@ expect cycles: 3 + 4 + 2 + 50 * 15 - 2 + 6
@ expect ret: 250
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
    ldr r1, =table
    ldr r2, =buf
    movs r4, #50
    movs r0, #0
loop:
    ldr r3, [r1]
    str r3, [r2]
    ldr r3, [r2]
    adds r0, r0, r3
    ldrb r3, [r1, #1]
    ldrh r3, [r1, #2]
    subs r4, #1
    bne loop
    pop {r4, pc}
    .size main, .-main
    .ltorg
    .section .rodata
    .balign 4
table: .word 5
    .bss
    .balign 4
buf: .space 4
