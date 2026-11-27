@ Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
@ Released under the MIT license as described in the file LICENSE.
@ Loads back to back and taken branches: eight blocks (LDR, LDR, B to the next block) and a
@ NOP, the pattern on which Lindner et al. (VMCAI 2026) found a WCET analyser's Cortex-M0
@ pipeline model unsound. 50 iterations.
@ Cycles (Cortex-M0 TRM, Table 3-1): push 3, ldr= 2, movs 1; per iteration 8 x (2 + 2 + 3) + nop 1
@ + subs 1 + bne 3 (1 the last time); adds 1, pop {r4, pc} 6.
@ expect cycles: 3 + 2 + 1 + 50 * 61 - 2 + 1 + 6
@ expect ret: 3
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
    ldr r1, =buf
    movs r4, #50
1:  ldr r2, [r1]
    ldr r3, [r1, #4]
    b 2f
2:  ldr r2, [r1]
    ldr r3, [r1, #4]
    b 3f
3:  ldr r2, [r1]
    ldr r3, [r1, #4]
    b 4f
4:  ldr r2, [r1]
    ldr r3, [r1, #4]
    b 5f
5:  ldr r2, [r1]
    ldr r3, [r1, #4]
    b 6f
6:  ldr r2, [r1]
    ldr r3, [r1, #4]
    b 7f
7:  ldr r2, [r1]
    ldr r3, [r1, #4]
    b 8f
8:  ldr r2, [r1]
    ldr r3, [r1, #4]
    b 9f
9:  nop
    subs r4, #1
    bne 1b
    adds r0, r2, r3
    pop {r4, pc}
    .size main, .-main
    .ltorg
    .data
    .balign 4
buf: .word 1, 2
