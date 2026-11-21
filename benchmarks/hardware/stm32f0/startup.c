/* Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
 * Released under the MIT license as described in the file LICENSE.
 *
 * Start-up code for measuring one TACLeBench kernel on an STM32F0 (Cortex-M0), linked with
 * the very object (KERNEL.m0.o) whose cycle bounds were computed and certified.
 *
 * Clock: the reset state (HSI 8 MHz, no PLL, AHB and APB prescalers 1, flash latency 0,
 * prefetch buffer on), so that memory has no wait states, as in the timing table of
 * m0.py and Thumb.decode. TIM2 (32 bits) counts at the APB clock = core clock. No interrupt
 * is enabled. The kernel's main is called once, after .data and .bss are set up (as in the
 * emulator), between two reads of TIM2_CNT; the same is done for an empty function to
 * measure the overhead of the reads and of the call. Result on USART2 (PA2, the ST-Link
 * virtual COM port of the Nucleo boards), 115200 baud 8N1:
 *     CROSSCHECK raw=<cycles> empty=<cycles> ret=<main's return value>
 * The register addresses are those of the STM32F0 reference manual (RM0091); they were
 * written from it and not yet tried on a board.
 */
#define REG(a) (*(volatile unsigned *)(a))
#define RCC_AHBENR REG(0x40021014u)
#define RCC_APB1ENR REG(0x4002101Cu)
#define FLASH_ACR REG(0x40022000u)
#define GPIOA_MODER REG(0x48000000u)
#define GPIOA_AFRL REG(0x48000020u)
#define TIM2_CR1 REG(0x40000000u)
#define TIM2_EGR REG(0x40000014u)
#define TIM2_PSC REG(0x40000028u)
#define TIM2_ARR REG(0x4000002Cu)
#define USART2_CR1 REG(0x40004400u)
#define USART2_BRR REG(0x4000440Cu)
#define USART2_ISR REG(0x4000441Cu)
#define USART2_TDR REG(0x40004428u)

extern int main(void);
extern unsigned _sidata, _sdata, _edata, _sbss, _ebss, _estack;

/* measure(f, &ret): cycles between two reads of TIM2_CNT around a call of f, in assembly
 * so that the sequence is the same for main and for the empty function */
unsigned measure(int (*f)(void), int *ret);
__asm__(".syntax unified\n.text\n.thumb\n.align 2\n.global measure\n.type measure, %function\n.thumb_func\n"
        "measure:\n"
        "  push {r4, r5, r6, r7, lr}\n"
        "  mov r6, r0\n"
        "  mov r7, r1\n"
        "  ldr r4, =0x40000024\n"
        "  ldr r5, [r4]\n"
        "  blx r6\n"
        "  ldr r1, [r4]\n"
        "  str r0, [r7]\n"
        "  subs r0, r1, r5\n"
        "  pop {r4, r5, r6, r7, pc}\n"
        ".ltorg\n");

__attribute__((noinline)) int empty(void) { return 0; }

static void putc_(char c) {
    while (!(USART2_ISR & (1u << 7))) {}   /* TXE */
    USART2_TDR = (unsigned char)c;
}
static void puts_(const char *s) { while (*s) putc_(*s++); }
static void putu(unsigned v) {
    char b[11]; int n = 0;
    do { b[n++] = (char)('0' + v % 10); v /= 10; } while (v);
    while (n) putc_(b[--n]);
}
static void puti(int v) { if (v < 0) { putc_('-'); putu(0u - (unsigned)v); } else putu((unsigned)v); }

void Reset_Handler(void) {
    unsigned *s = &_sidata, *d = &_sdata;
    while (d < &_edata) *d++ = *s++;
    for (d = &_sbss; d < &_ebss; ) *d++ = 0;
    FLASH_ACR = (FLASH_ACR & ~7u);                 /* latency 0 (the reset value) */
    RCC_AHBENR |= 1u << 17;                        /* GPIOA */
    RCC_APB1ENR |= (1u << 0) | (1u << 17);         /* TIM2, USART2 */
    GPIOA_MODER = (GPIOA_MODER & ~(3u << 4)) | (2u << 4);    /* PA2 alternate function */
    GPIOA_AFRL = (GPIOA_AFRL & ~(15u << 8)) | (1u << 8);     /* AF1 = USART2_TX */
    USART2_BRR = 69;                               /* 8 MHz / 115200 */
    USART2_CR1 = (1u << 3) | 1u;                   /* TE, UE */
    TIM2_PSC = 0;
    TIM2_ARR = 0xFFFFFFFFu;
    TIM2_EGR = 1;                                  /* load PSC */
    TIM2_CR1 = 1;                                  /* count */
    int r, ret;
    unsigned e = measure(empty, &r), k;
    for (k = 0; k < 3; k++) { unsigned x = measure(empty, &r); if (x < e) e = x; }
    unsigned raw = measure(main, &ret);
    puts_("CROSSCHECK raw="); putu(raw);
    puts_(" empty="); putu(e);
    puts_(" ret="); puti(ret);
    puts_("\r\n");
    for (;;) {}
}

void Fault_Handler(void) {
    puts_("CROSSCHECK fault\r\n");
    for (;;) {}
}

__attribute__((section(".isr_vector"), used))
static void *const vectors[16] = {
    &_estack, (void *)Reset_Handler, (void *)Fault_Handler, (void *)Fault_Handler,
};
