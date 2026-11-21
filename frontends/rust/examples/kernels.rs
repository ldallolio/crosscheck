// Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
// Released under the MIT license as described in the file LICENSE.
// Small real-time kernels in Rust for the Rust front-end (frontends/rust).
// Functions named `rejected_*` must receive no bound; every other one should be bounded.
// `assert!` states the input ranges: it is checked at run time, so nothing is trusted.

/// FIR filter step: at most 32 taps.
pub fn fir(x: &[i32], h: &[i32]) -> i32 {
    assert!(h.len() <= 32);
    let mut acc: i32 = 0;
    let mut k = 0usize;
    while k < h.len() && k < x.len() {
        acc = acc.wrapping_add(x[k].wrapping_mul(h[k]));
        k += 1;
    }
    acc
}

/// Saturating accumulation of a block of at most 256 samples.
pub fn sat_sum(x: &[i16]) -> i32 {
    assert!(x.len() <= 256);
    let mut s: i32 = 0;
    for i in 0..x.len() {
        s += x[i] as i32;
        if s > 30000 {
            s = 30000;
        } else if s < -30000 {
            s = -30000;
        }
    }
    s
}

/// Bubble sort of at most 64 elements.
pub fn bubble(a: &mut [i32]) -> i32 {
    assert!(a.len() <= 64);
    let n = a.len();
    let mut swaps = 0;
    for i in 0..n {
        for j in 0..n - 1 - i {
            if a[j] > a[j + 1] {
                let t = a[j];
                a[j] = a[j + 1];
                a[j + 1] = t;
                swaps += 1;
            }
        }
    }
    swaps
}

/// Integer square root by a counting loop, for x <= 10000.
pub fn isqrt(x: u32) -> u32 {
    assert!(x <= 10000);
    let mut r: u32 = 0;
    while (r + 1) * (r + 1) <= x {
        r += 1;
    }
    r
}

/// Count of the values above a threshold.
pub fn count_above(x: &[i32], t: i32) -> u32 {
    assert!(x.len() <= 1000);
    let mut c = 0u32;
    for &v in x.iter() {
        if v > t {
            c += 1;
        }
    }
    c
}

/// A counter that goes down by 7 from at most 7000.
pub fn steps_down(mut n: i32) -> i32 {
    assert!(n <= 7000);
    let mut k = 0;
    while n > 0 {
        n -= 7;
        k += 1;
    }
    k
}

/// A loop with a constant bound and a nested condition.
pub fn table() -> i32 {
    let mut acc = 0;
    let mut i = 0;
    while i < 100 {
        if i % 3 == 0 {
            acc += i;
        } else {
            acc -= 1;
        }
        i += 1;
    }
    acc
}

/// Calls of bounded functions.
pub fn twice(n: i32) -> i32 {
    steps_down(n) + steps_down(n / 2)
}

/// Euclid's algorithm: logarithmic, not linear in the inputs; must be rejected.
pub fn rejected_gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Collatz: termination unknown; must be rejected.
pub fn rejected_collatz(mut n: u64) -> u32 {
    assert!(n >= 1 && n <= 1000);
    let mut k = 0u32;
    while n != 1 {
        n = if n % 2 == 0 { n / 2 } else { 3 * n + 1 };
        k += 1;
    }
    k
}

/// A wrapping counter that never meets its exit value: does not terminate; must be rejected.
pub fn rejected_wrap(start: u8) -> u8 {
    let mut i = start & 0xFE;
    let mut k: u8 = 0;
    while i != 255 {
        i = i.wrapping_add(2);
        k = k.wrapping_add(1);
    }
    k
}

/// Terminates only by overflow (a panic): no bound for the executions that do not panic.
pub fn rejected_overflow(mut i: i32) -> i32 {
    while i >= 0 {
        i += 1;
    }
    i
}
