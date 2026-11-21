// Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
// Released under the MIT license as described in the file LICENSE.
// Products of parameters (option `symbolic`, no input ranges): a nest whose entry bounds
// are both parameters has a certified bound quadratic in them (Lean `loopBoundOk`, third
// form: `(w + Wb) * max(0, K) + w`), and a call instantiates the callee's quadratic terms
// with the products of the bounds of its arguments (`callBound`, `SB.qcomb`).
// The certificate of this file is formalization/test/certificates/products.json.
#include <crosscheck/attributes.hpp>
CROSSCHECK_REALTIME int rect(int n, int m) {
  int s = 0;
  for (int i = 0; i < n; i++)
    for (int j = 0; j < m; j++) s++;
  return s;
}
CROSSCHECK_REALTIME int square(int n) {
  int s = 0;
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) s++;
  return s;
}
CROSSCHECK_REALTIME int caller(int k) {
  return rect(k, k + 2) + square(3);
}
