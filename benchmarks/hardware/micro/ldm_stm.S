@ Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
@ Released under the MIT license as described in the file LICENSE.
@ LDM and STM of four registers with write-back, in RAM. 50 iterations.
@ Cycles: push {r4-r7, lr} 6, ldr= 2, movs 1; per iteration ldm 5, subs 1, stm 5, subs 1, subs 1,
@ bne 3 (1 the last time); movs 1, pop {r4-r7, pc} 9.
@ expect cycles: 6 + 2 + 1 + 50 * 16 - 2 + 1 + 9
@ expect ret: 4
    .syntax unified
    .cpu cortex-m0
    .thumb
    .text
    .balign 4
    .global main
    .type main, %function
    .thumb_func
main:
    push {r4-r7, lr}
    ldr r0, =buf
    movs r7, #50
loop:
    ldm r0!, {r1-r4}
    subs r0, #16
    stm r0!, {r1-r4}
    subs r0, #16
    subs r7, #1
    bne loop
    movs r0, r4
    pop {r4-r7, pc}
    .size main, .-main
    .ltorg
    .data
    .balign 4
buf: .word 1, 2, 3, 4
