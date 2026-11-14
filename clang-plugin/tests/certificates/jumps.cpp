// Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
//
// Early exits, switch and && loop tests: every function must get a certificate
// that the Lean checker accepts (tests/check_certificates.sh).
#include <crosscheck/attributes.hpp>
CROSSCHECK_REALTIME int brk(CROSSCHECK_RANGE(0, 50) int n, const int* c) {
  int x = 0;
  while (x < n) { if (c[x]) break; x++; }
  int s = 0;
  while (x < n) { x++; s++; }
  return s;
}
CROSSCHECK_REALTIME int cont(CROSSCHECK_RANGE(0, 20) int n, const int* c) {
  int s = 0;
  for (int i = 0; i < n; i++) { if (c[i]) continue; s += 2; }
  return s;
}
CROSSCHECK_REALTIME int find(CROSSCHECK_RANGE(0, 30) int n, const int* a, int key) {
  for (int i = 0; i < n; i++)
    if (a[i] == key) return i;
  return -1;
}
CROSSCHECK_REALTIME int both(CROSSCHECK_RANGE(0, 30) int n, const int* a) {
  int i = 0;
  while (i < n && a[i] != 0) i++;
  return i;
}
CROSSCHECK_REALTIME int sw(int op, CROSSCHECK_RANGE(0, 10) int n) {
  int s = 0;
  switch (op) {
    case 0: s = 1; break;
    case 1: for (int i = 0; i < n; i++) s += 2; break;
    case 2:
    case 3: return 7;
    default: s = 3;
  }
  return s;
}
CROSSCHECK_REALTIME int nested(CROSSCHECK_RANGE(0, 8) int n, const int* m) {
  int s = 0;
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      if (m[i * 8 + j] < 0) return -1;
      if (m[j] == 0) break;
      s++;
    }
  }
  return s;
}
CROSSCHECK_REALTIME int fallthrough(int op, CROSSCHECK_RANGE(0, 10) int n) {
  int s = 0;
  switch (op) {
    case 0: s = 5;
    case 1: for (int i = 0; i < n; i++) s++;
            break;
    default: return 0;
  }
  return s;
}
CROSSCHECK_REALTIME int cont_while(CROSSCHECK_RANGE(0, 20) int n, const int* c) {
  int i = 0, s = 0;
  while (i < n) {
    i++;
    if (c[i - 1]) continue;
    s++;
  }
  return s;
}
// A callee's `return` ends the callee only, also when it is inlined inside a loop.
static int clip(int v) {
  if (v < 0) return 0;
  return v;
}
CROSSCHECK_REALTIME int inlined_return(CROSSCHECK_RANGE(0, 16) int n, const int* a) {
  int s = 0;
  for (int i = 0; i < n; i++) s += clip(a[i]);
  return s;
}
