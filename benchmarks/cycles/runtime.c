/* Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
   Released under the MIT license as described in the file LICENSE.

   Integer division for the Cortex-M0 (which has no divide instruction), with the run-time
   ABI names that Clang calls for `/` and `%`: restoring division, 32 iterations, so that
   CrossCheck bounds its loop and the cycle analysis covers code that divides. Division by
   zero returns 0 (the ABI leaves it to the implementation). No `/` or `%` is used here. */

unsigned long long __aeabi_uidivmod(unsigned n, unsigned d) {
  unsigned q = 0, r = 0;
  if (d == 0) return 0;
  for (int i = 31; i >= 0; i--) {
    r = (r << 1) | ((n >> i) & 1u);
    if (r >= d) {
      r = r - d;
      q = q | (1u << i);
    }
  }
  return (unsigned long long)q | ((unsigned long long)r << 32);
}

unsigned __aeabi_uidiv(unsigned n, unsigned d) { return (unsigned)__aeabi_uidivmod(n, d); }

long long __aeabi_idivmod(int n, int d) {
  unsigned un = n < 0 ? 0u - (unsigned)n : (unsigned)n;
  unsigned ud = d < 0 ? 0u - (unsigned)d : (unsigned)d;
  unsigned long long qr = __aeabi_uidivmod(un, ud);
  unsigned q = (unsigned)qr, r = (unsigned)(qr >> 32);
  if ((n < 0) != (d < 0)) q = 0u - q;
  if (n < 0) r = 0u - r;
  return (long long)((unsigned long long)q | ((unsigned long long)r << 32));
}

int __aeabi_idiv(int n, int d) { return (int)(unsigned)__aeabi_idivmod(n, d); }
