/* Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
   Released under the MIT license as described in the file LICENSE. */
/* Functions exercising the instruction classes of the Cortex-M0, for test_m0.py. */
int t_asr(int a, int b) { return a >> (b & 31); }
unsigned t_lsr(unsigned a, unsigned b) { return a >> (b & 31); }
unsigned t_lsl(unsigned a, unsigned b) { return a << (b & 31); }
int t_mul(int a, int b) { return a * b; }
int t_lt(int a, int b) { return a < b; }
int t_le(int a, int b) { return a <= b; }
int t_ult(unsigned a, unsigned b) { return a < b; }
int t_ugt(unsigned a, unsigned b) { return a > b; }
long long t_add64(long long a, long long b) { return a + b; }
long long t_sub64(long long a, long long b) { return a - b; }
long long t_mul64(int a, int b) { return (long long)a * b; }
int t_sxtb(int a) { return (signed char)a; }
int t_sxth(int a) { return (short)a; }
unsigned t_uxtb(unsigned a) { return (unsigned char)a; }
unsigned t_rev(unsigned a) { return __builtin_bswap32(a); }
int t_asr3(int a) { return a >> 13; }
int t_neg(int a) { return -a; }
int t_bic(int a, int b) { return a & ~b; }
int t_div(int a, int b) { return b ? a / b : 0; }
int t_mod(int a, int b) { return b ? a % b : 0; }
unsigned t_udiv(unsigned a, unsigned b) { return b ? a / b : 0; }
int t_loop(int n) { int s = 0; for (int i = 0; i < (n & 63); i++) s += i * i - (s >> 2); return s; }
int t_fft(int l, int k, int p0, int p1) {
  int tmpr = l * p0; tmpr -= k * p1; int tmpi = l * p1; tmpi += k * p0;
  tmpr >>= 13; tmpi >>= 13; return tmpr ^ (tmpi << 3);
}
int t_buf[64];
int t_bitrev(int seed) {
  int i, j = 0, m, n = 64, tmpr;
  for (i = 0; i < 64; i++) t_buf[i] = seed + 7 * i;
  for (i = 0; i < (n - 1); i += 2) {
    if (j > i) {
      tmpr = t_buf[j]; t_buf[j] = t_buf[i]; t_buf[i] = tmpr;
      tmpr = t_buf[j + 1]; t_buf[j + 1] = t_buf[i + 1]; t_buf[i + 1] = tmpr;
    }
    m = 32;
    while (m >= 2 && j >= m) { j -= m; m >>= 1; }
    j += m;
  }
  int s = 0;
  for (i = 0; i < 64; i++) s = s * 31 + t_buf[i];
  return s;
}
