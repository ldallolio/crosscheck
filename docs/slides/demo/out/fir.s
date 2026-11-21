
docs/slides/demo/out/fir.o:	file format elf32-littlearm

Disassembly of section .text:

00000000 <dot>:
; dot():
; ./docs/slides/demo/fir.c:12
       0:      	push	{r4, r5, r7, lr}
       2:      	add	r7, sp, #0x8
; ./docs/slides/demo/fir.c:14
       4:      	lsls	r0, r0, #0x2
       6:      	ldr	r1, [pc, #0x18]         @ 0x20 <dot+0x20>
       8:      	adds	r1, r1, r0
       a:      	movs	r2, #0x0
       c:      	ldr	r3, [pc, #0x14]         @ 0x24 <dot+0x24>
       e:      	mov	r0, r2
; ./docs/slides/demo/fir.c:15
      10:      	ldr	r4, [r3, r2]
      12:      	ldr	r5, [r1, r2]
      14:      	muls	r5, r4, r5
      16:      	adds	r0, r5, r0
; ./docs/slides/demo/fir.c:14
      18:      	adds	r2, r2, #0x4
      1a:      	cmp	r2, #0x20
      1c:      	bne	0x10 <dot+0x10>         @ imm = #-0x10
; ./docs/slides/demo/fir.c:16
      1e:      	pop	{r4, r5, r7, pc}
      20: 00 00 00 00  	.word	0x00000000
      24: 00 00 00 00  	.word	0x00000000

00000028 <fir_peak>:
; fir_peak():
; ./docs/slides/demo/fir.c:20
      28:      	push	{r4, r5, r6, r7, lr}
      2a:      	add	r7, sp, #0xc
      2c:      	sub	sp, #0x4
      2e:      	str	r0, [sp]
; ./docs/slides/demo/fir.c:22
      30:      	cmp	r0, #0x1
      32:      	blt	0x52 <fir_peak+0x2a>    @ imm = #0x1c
      34:      	mov	r4, r0
      36:      	movs	r6, #0x0
      38:      	mov	r5, r6
      3a:      	b	0x44 <fir_peak+0x1c>    @ imm = #0x6
; ./docs/slides/demo/fir.c:22
      3c:      	adds	r5, r5, #0x1
      3e:      	cmp	r4, r5
      40:      	mov	r6, r0
      42:      	beq	0x54 <fir_peak+0x2c>    @ imm = #0xe
; ./docs/slides/demo/fir.c:23
      44:      	mov	r0, r5
      46:      	bl	0x46 <fir_peak+0x1e>    @ imm = #-0x4
; ./docs/slides/demo/fir.c:24
      4a:      	cmp	r0, r6
      4c:      	bgt	0x3c <fir_peak+0x14>    @ imm = #-0x14
      4e:      	mov	r0, r6
      50:      	b	0x3c <fir_peak+0x14>    @ imm = #-0x18
      52:      	movs	r0, #0x0
; ./docs/slides/demo/fir.c:26
      54:      	add	sp, #0x4
      56:      	pop	{r4, r5, r6, r7, pc}
