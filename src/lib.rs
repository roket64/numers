// Copyright (c) 2023 roket64.
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

pub mod error;

use num_integer::Integer;
use num_integer::Roots;
use rand::random;

use std::fmt::{Display, Formatter};
use std::mem;
use std::vec::Vec;

use error::{ArithmeticError, ArithmeticErrorKind};

/// Structure represents the Bézout's Identity. \
/// `a_coeff` represents `x` and `b_coeff` represents `y` from
/// equation `ax + by = gcd(a, b)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BezoutIdentity<T: Int> {
    pub gcd: T,
    pub a_coeff: i64,
    pub b_coeff: i64,
}

macro_rules! impl_bezoutid {
    ($($t: ty),+) => {$(
        impl Display for BezoutIdentity<$t> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}a + {}b = {}",
                     self.a_coeff, self.b_coeff, self.gcd)
            }
        }
    )+};
}

impl_bezoutid!(isize, i32, i64, usize, u32, u64);

pub trait Int: Integer {
    /// Calculates greatest common divisor of given integers and returns the Bézout's Identity,
    /// which is the solution to the equation `ax + by = gcd(a, b)`.
    fn ext_gcd(&self, other: &Self) -> Result<BezoutIdentity<Self>, ArithmeticError>;

    /// Returns `Option<Vec<Self>>` containing non-trivial divisors of the given integer
    /// wrapped `Result` wether the calculation was successful.
    fn factors(&self) -> Result<Option<Vec<Self>>, ArithmeticError>;

    /// Factorizes an single integer and returns `Vec` containing non-trivial divisors. \
    /// Time complexity is `O(n^¼)`, since it's a variant of Pollard-rho algorithm.
    fn factorize(&self) -> Result<Vec<Self>, ArithmeticError>;

    /// Calculates least nonnegative integer from modular multiplication between given integers
    /// and returns `Result<T, ArithmeticError>` wether the calculation was successful.
    /// # Examples
    /// ```
    /// let n: i32 = 5;
    /// let m: i32 = 10;
    /// let k: i32 = 7;
    /// assert_eq!(modular_mul(n, m, k).unwrap(), 1);
    /// ```
    fn modular_mul(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError>;

    /// Calculates least nonnegative ineger from modular exponentiation between given integers
    /// and returns `Result<T, ArithmeticError>` wether the calculation was successful.
    /// Since we are interested in integers only, the result on negative exponent will return 0. \
    /// This implements the Binary Exponentiation Algorithm, hence the time complexity on
    /// integer `x^y (mod n)` is `O(log2(y))`.
    /// # Examples
    /// ```
    /// let n: i32 = 2;
    /// let m: i32 = 3;
    /// let k: i32 = 4;
    /// assert_eq!(modular_pow(n, m, k).unwrap(), 0);
    /// ```
    fn modular_pow(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError>;

    /// Tests primality of the given intger and returns `bool` wether the integer is prime. \
    /// This implementation is a variant of Miller-Rabin Primality Test,
    /// hecne time complexity is `O(log^3N)`. Works deterministically
    /// for 64-bit integers, and the probobility of returning `true` for pseudoprime
    /// is `0.25^20 * ln(n)`.
    /// # Examples
    /// ```
    /// let n = 561; // Carmichael number
    /// let m = 100000007;
    /// assert!(!n.is_prime());
    /// assert!(n.is_prime());
    /// ```
    /// # Panic
    /// Basically this function will return `ArithmeticError` when
    /// the computation was not successful, but still could panic
    /// on unexpected situations or undefined behaviors.
    fn is_prime(&self) -> Result<bool, ArithmeticError>;

    /// returns square root of `&self` modulo p
    /// modulus value must be a prime.
    fn modular_sqrt(&self, modulus: &Self) -> Result<Self, ArithmeticError>;

    /// returns the number of primes smaller or equal to `&self`
    fn pi(&self) -> Result<usize, ArithmeticError>;

    /// returns the number of integers that is coprime to `&self`
    fn euler_phi(&self) -> Result<usize, ArithmeticError>;

    /// returns the number of positive factors of `&self`
    fn tau(&self) -> Result<usize, ArithmeticError>;

    /// returns the sum of positive factors including trivial divisors of `&self`
    fn sigma(&self) -> Result<usize, ArithmeticError>;

    /// returns the number of prime factors of `&self`
    fn omega(&self) -> Result<usize, ArithmeticError>;

    /// returns the Jacobi Symbol of the given integer.
    fn jacobi(&self) -> Result<isize, ArithmeticError>;
}

/// Calculates Greatest Common Divior and Bézout's Identity
pub fn ext_gcd<T: Int>(x: T, y: T) -> Result<BezoutIdentity<T>, ArithmeticError> {
    x.ext_gcd(&y)
}

// Factors of an integer
pub fn factors<T: Int>(x: T) -> Result<Option<Vec<T>>, ArithmeticError> {
    x.factors()
}

/// Factorizes an integer
pub fn factorize<T: Int>(x: T) -> Result<Vec<T>, ArithmeticError> {
    x.factorize()
}

/// Returns least nonnegative integer from modular multiplication
pub fn modular_mul<T: Int>(x: T, y: T, modulus: T) -> Result<T, ArithmeticError> {
    x.modular_mul(&y, &modulus)
}

/// Returns least nonnegative integer from modular exponentiation
pub fn modular_pow<T: Int>(base: T, exponent: T, modulus: T) -> Result<T, ArithmeticError> {
    base.modular_pow(&exponent, &modulus)
}

/// Returns bool wether the given integer is prime number
pub fn is_prime<T: Int>(x: T) -> Result<bool, ArithmeticError> {
    x.is_prime()
}

fn modular_sqrt<T: Int>(x: T, modulus: T) -> Result<T, ArithmeticError> {
    x.modular_sqrt(&modulus)
}

/// returns the number of primes smaller or equal to `&self`
fn pi<T: Int>(x: T) -> Result<usize, ArithmeticError> {
    x.pi()
}

/// returns the number of integers that is coprime to `&self`
fn euler_phi<T: Int>(x: T) -> Result<usize, ArithmeticError> {
    x.euler_phi()
}

/// returns the number of positive factors of `&self`
fn tau<T: Int>(x: T) -> Result<usize, ArithmeticError> {
    x.tau()
}

/// returns the sum of positive factors including trivial divisors of `&self`
fn sigma<T: Int>(x: T) -> Result<usize, ArithmeticError> {
    x.sigma()
}

/// returns the number of prime factors of `&self`
fn omega<T: Int>(x: T) -> Result<usize, ArithmeticError> {
    x.omega()
}

/// returns the Jacobi Symbol of the given integer.
fn jacobi<T: Int>(x: T) -> Result<isize, ArithmeticError> {
    x.jacobi()
}

macro_rules! impl_int_isize {
    ($($t: ty, $test_mod: ident);+) => {$(
        impl Int for $t {
            fn ext_gcd(&self, other: &Self) -> Result<BezoutIdentity<Self>, ArithmeticError> {
                if *self == 0 {
                    return Ok(BezoutIdentity {
                        gcd: *other as $t,
                        a_coeff: 0,
                        b_coeff: 1,
                    })
                }
                if *other == 0 {
                    return Ok(BezoutIdentity {
                        gcd: *self as $t,
                        a_coeff: 1,
                        b_coeff: 0,
                    })
                }

                let mut a0: i64 = *self as i64;
                let mut b0: i64 = *other as i64;

                let mut x0: i64 = 1;
                let mut x1: i64 = 0;
                let mut y0: i64 = 0;
                let mut y1: i64 = 1;

                while b0 != 0 {
                    let q: i64 = a0 / b0;
                    (x0, x1) = (x1, x0 - q * x1);
                    (y0, y1) = (y1, y0 - q * y1);
                    (a0, b0) = (b0, a0 - q * b0);
                }

                if a0 > 0 {
                    Ok(BezoutIdentity {
                        gcd: a0.abs() as $t,
                        a_coeff: x0,
                        b_coeff: y0,
                    })
                } else {
                    Ok(BezoutIdentity {
                        gcd: a0.abs() as $t,
                        a_coeff: -x0,
                        b_coeff: -y0,
                    })
                }
            }

            fn factors(&self) -> Result<Option<Vec<Self>>, ArithmeticError> {
                let is_neg = *self < 0;
                let x: $t = self.abs();
                let mut res: Vec::<Self> = vec![];

                for i in 2..=x.sqrt() {
                    if x % i == 0 {
                        match i * i == x {
                            true => {
                                res.push(i);
                            },
                            false => {
                                res.push(i);
                                res.push(x / i);
                            }
                        }
                    }
                }
                res.sort();

                if res.len() > 0 {
                    if is_neg {
                        res[0] = -res[0];
                    }

                    return Ok(Some(res));
                }

                Ok(None)
            }

            fn factorize(&self) -> Result<Vec<Self>, ArithmeticError> {
                // TODO: implmented trial division instead for now
                let mut x: $t = *self;
                let mut res: Vec::<Self> = vec![];

                for i in 2..x.sqrt() {
                    while x % i == 0 {
                        res.push(i);
                        x /= i;
                    }
                }
                if x > 1 {
                    res.push(x)
                }
                res.sort();

                Ok(res)
            }

            fn modular_mul(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError> {
                // all arguments will be casted internally into i128 to avoid overflow
                let mut res: i128 = match *modulus != 0 {
                    true => 0,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    }
                };

                let mut x: i128 = *self as i128;
                let mut y: i128 = match *other < 0 {
                    true => -(*other as i128),
                    false => *other as i128,
                };
                let m: i128 = *modulus as i128;

                while y != 0 {
                    if y & 1 == 1 {
                        res = match res.checked_add(x) {
                            // using rem_euclid() since we want a nonnegative remainder
                            Some(n) => n.rem_euclid(m),
                            None => {
                                return Err(ArithmeticError {
                                    kind: ArithmeticErrorKind::OVERFLOW,
                                })
                            }
                        };
                    }

                    x = match x.checked_mul(2) {
                        Some(n) => n.rem_euclid(2),
                        None => {
                            return Err(ArithmeticError {
                                kind: ArithmeticErrorKind::OVERFLOW,
                            })
                        }
                    };
                    y >>= 1;
                }

                // shrink result into return type
                Ok(res as $t)
            }

            fn modular_pow(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError> {
                // all arguments will be casted internally into i128 to avoid overflow
                let mut res: i128 = match *modulus != 0 {
                    true => 1,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    }
                };

                let mut x: i128 = *self as i128;
                // negative exponent will return 0
                let mut y: i128 = match *other < 0 {
                    true => return Ok(0),
                    false => *other as i128,
                };
                let m: i128 = *modulus as i128;

                x %= m;

                while y != 0 {
                    if y & 1 == 1 {
                        res = match res.checked_mul(x) {
                            Some(n) => n.rem_euclid(m),
                            None => {
                                return Err(ArithmeticError {
                                    kind: ArithmeticErrorKind::OVERFLOW,
                                })
                            }
                        };
                    }

                    x = match x.checked_mul(x) {
                        Some(n) => n.rem_euclid(m),
                        None => {
                            return Err(ArithmeticError {
                                kind: ArithmeticErrorKind::OVERFLOW,
                            })
                        }
                    };
                    y >>= 1;
                }

                // shrink result into return type
                Ok(res as $t)
            }

            fn is_prime(&self) -> Result<bool, ArithmeticError> {
                let n = *self;

                if n == 2 || n == 3 || n == 5 || n == 7 {
                    return Ok(true);
                }
                if n % 2 == 0 || n % 3 == 0 || n % 5 == 0 || n % 7 == 0 {
                    return Ok(false);
                }
                if n < 121 {
                    return Ok(n > 1);
                }

                // finding d, s that satisfies n = d * 2^s
                let bin_expan = |n: i128| {
                    let mut d = n;
                    let mut s = 0;
                    while (d & 1) == 0 {
                        s += 1;
                        d >>= 1;
                    }
                    (d, s)
                };

                // Michal Forisek's Algorithm for 32-bit integer
                let _is_prime32 = |n: $t| {
                    let base: Vec<i128> = vec![
                        0x3ce7, 0x7e2, 0xa6, 0x1d05, 0x1f80, 0x3ead, 0x2907, 0x112f, 0x79d, 0x50f, 0xad8, 0xe24,
                        0x230, 0xc38, 0x145c, 0xa61, 0x8fc, 0x7e5, 0x122c, 0x5bf, 0x2478, 0xfb2, 0x95e, 0x4fee,
                        0x2825, 0x1f5c, 0x8a5, 0x184b, 0x26c, 0xeb3, 0x12f4, 0x1394, 0xc71, 0x535, 0x1853, 0x14b2,
                        0x432, 0x957, 0x13f9, 0x1b95, 0x323, 0x4f5, 0xf23, 0x1a6, 0x2ef, 0x244, 0x1279, 0x27ff,
                        0x2ea, 0xb87, 0x22c, 0x89e, 0xec2, 0x1e1, 0x5f2, 0xd94, 0x1e1, 0x9b7, 0xcc2, 0x1601, 0x1e8,
                        0xd2d, 0x1929, 0xd10, 0x11, 0x3b01, 0x5d2, 0x103a, 0x7f4, 0x75a, 0x715, 0x1d3, 0xceb,
                        0x36da, 0x18e3, 0x292, 0x3ed, 0x387, 0x2e1, 0x75f, 0x1d17, 0x760, 0xb20, 0x6f8, 0x1d87,
                        0xd48, 0x3b7, 0x3691, 0x10d0, 0xb1, 0x29, 0x4da3, 0xc26, 0x33a5, 0x2216, 0x23b, 0x1b83,
                        0x1b1f, 0x4af, 0x160, 0x1923, 0xa5, 0x491, 0xcf3, 0x3d2, 0xe9, 0xbbb, 0xa02, 0xbb2, 0x295b,
                        0x272e, 0x949, 0x76e, 0x14ea, 0x115f, 0x613, 0x107, 0x6993, 0x8eb, 0x131, 0x29d, 0x778,
                        0x259, 0x182a, 0x1ad, 0x78a, 0x3a19, 0x6f8, 0x67d, 0x20c, 0xdf9, 0xec, 0x938, 0x1802,
                        0xb22, 0xd955, 0x6d9, 0x1052, 0x2112, 0xde, 0xa13, 0xab7, 0x7ef, 0x8b2, 0x8e4, 0x176,
                        0x854, 0x32d, 0x5cec, 0x64a, 0x1146, 0x1427, 0x6bd, 0xe0d, 0xd26, 0x3800, 0x243, 0xa5,
                        0x55f, 0x2722, 0x3148, 0x2658, 0x55b, 0x218, 0x74b, 0x2a70, 0x359, 0x89e, 0x169c, 0x1b2,
                        0x1f95, 0x44d2, 0x2d7, 0xe37, 0x63b, 0x1350, 0x851, 0x7ed, 0x2003, 0x2098, 0x1858, 0x23df,
                        0x1fbe, 0x74e, 0xce0, 0x1d1f, 0x22f3, 0x61b9, 0x21d, 0x4aab, 0x170, 0x236, 0x162a, 0x19b,
                        0x20a, 0x403, 0x2017, 0x802, 0x1990, 0x2741, 0x266, 0x306, 0x91d, 0xbbf, 0x8981, 0x1262,
                        0x480, 0x6f9, 0x404, 0x604, 0xe9f, 0x1ed, 0x117a, 0x9d9, 0x68dd, 0x20a2, 0x360, 0x49e3,
                        0x1559, 0x98f, 0x2a, 0x119f, 0x67c, 0xa6, 0x4e1, 0x1873, 0x9f9, 0x130, 0x110, 0x1c76, 0x49,
                        0x199a, 0x383, 0xb00, 0x144d, 0x3412, 0x1b8e, 0xb02, 0xc7f, 0x32b, 0x39a, 0x15e, 0x1d5a,
                        0x1164, 0xd79, 0xa67, 0x1264, 0x1a2, 0x655, 0x493, 0xd8f, 0x58, 0x2c51, 0x19c, 0x617, 0xc2,
                    ];

                    let is_sprp = |n: i128, a: i128| {
                        let (d, s) = bin_expan(n - 1);
                        let mut x = a.modular_pow(&d, &n).unwrap();
                        if x == 1 {
                            return true;
                        }
                        for _ in 0..s {
                            if x == n - 1 {
                                return true;
                            }
                            x = x.modular_pow(&2, &n).unwrap();
                        }
                        false
                    };

                    // all variables must be u128 to handle operation below
                    let mut h = n as u128;
                    h = ((h >> 16) ^ h) * 0x45d9f3b;
                    h = ((h >> 16) ^ h) * 0x45d9f3b;
                    h = ((h >> 16) ^ h) & 255;

                    is_sprp(n as i128, base[h as usize])
                };

                // Miller-Rabin Algorithm for 64-bit integer
                let _is_prime64 = |n: $t| {
                    let f = |n: i128, a: i128| {
                        if n == a {
                            return true;
                        }
                        let (d, s) = bin_expan(n - 1);
                        let mut x = a.modular_pow(&d, &n).unwrap();
                        if x == 1 {
                            return true;
                        }
                        for _ in 0..s {
                            if x == n - 1 {
                                return true;
                            }
                            x = x.modular_pow(&2, &n).unwrap();
                        }
                        false
                    };

                    let base64: Vec<i128> = vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

                    for a in base64 {
                        if !f(n as i128, a) {
                            return false;
                        }
                    }
                    true
                };

                // Iterative Miller-Rabin Algorithm for 128-bit integer
                let _is_prime128 = |n: $t, iter: usize | {
                    let f = |n: i128, a: i128| {
                        let (d, s) = bin_expan(n - 1);
                        let mut x = a.modular_pow(&d, &n).unwrap();
                        if x == 1 {
                            return true;
                        }
                        for _ in 0..s {
                            if x == n - 1 {
                                return true;
                            }
                            x = x.modular_pow(&2, &n).unwrap();
                        }
                        false
                    };

                    for _ in 0..iter {
                        // pick an random integer between [2, n - 2]
                        let a = 2 + random::<i128>().abs() % (n - 4) as i128;
                        if !f(n as i128, a) {
                            return false;
                        }
                    }
                    true
                };

                let sz = mem::size_of::<$t>();

                if sz <= 4 {
                    // test for 32-bit size integers
                    // works deterministically
                    Ok(_is_prime32(n))
                } else if 4 < sz && sz <= 8 {
                    // test for 64-bit size integers
                    // works deterministically
                    Ok(_is_prime64(n))
                } else {
                    // probabilistic test for 128-bit size integers,
                    // probobility of returning true for pseudoprime
                    // is approximate to 0.25^20 * ln(n)
                    Ok(_is_prime128(n, 20))
                }
            }

            fn modular_sqrt(&self, modulus: &Self) -> Result<Self, ArithmeticError> {
                unimplemented!()
            }

            fn pi(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            fn euler_phi(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            fn tau(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            fn sigma(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            fn omega(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            fn jacobi(&self) -> Result<isize, ArithmeticError> {
                unimplemented!()
            }
        }

        #[cfg(test)]
        mod $test_mod {
            #[test]
            fn test_gcd() {
                todo!()
            }

            #[test]
            fn test_ext_gcd() {
                todo!()
            }

            #[test]
            fn test_factorize() {
                todo!()
            }

            #[test]
            fn test_modular_mul() {
                todo!()
            }

            #[test]
            fn test_modular_pow() {
                todo!()
            }
        }
    )+};
}

macro_rules! impl_int_usize {
    ($($t: ty, $test_mod: ident);+) => {$(
        impl Int for $t {
            // Extended Euclidean Algorithm implementation
            fn ext_gcd(&self, other: &Self) -> Result<BezoutIdentity<Self>, ArithmeticError> {
                // All arguments and variables must be signed values,
                // since Bezout's Identity can have negative coefficients.
                if *self == 0 {
                    return Ok(BezoutIdentity {
                        gcd: *other as $t,
                        a_coeff: 0,
                        b_coeff: 1,
                    })
                }
                if *other == 0 {
                    return Ok(BezoutIdentity {
                        gcd: *self as $t,
                        a_coeff: 1,
                        b_coeff: 0,
                    })
                }

                // TODO: This may panic when size of `*self` doesn't fit to `i64`
                let mut a0 = *self as i64;
                let mut b0 = *other as i64;

                let mut x0: i64 = 1;
                let mut x1: i64 = 0;
                let mut y0: i64 = 0;
                let mut y1: i64 = 1;

                while b0 != 0 {
                    let q: i64 = a0 / b0;
                    (x0, x1) = (x1, x0 - q * x1);
                    (y0, y1) = (y1, y0 - q * y1);
                    (a0, b0) = (b0, a0 - q * b0);
                }

                Ok(BezoutIdentity {
                    gcd: a0 as $t,
                    a_coeff: x0,
                    b_coeff: y0,
                })
            }

            fn factors(&self) -> Result<Option<Vec<Self>>, ArithmeticError> {
                let x: $t = *self;
                let mut res: Vec::<Self> = vec![];

                for i in 2..=x.sqrt() {
                    if x % i == 0 {
                        match i * i == x {
                            true => {
                                res.push(i);
                            },
                            false => {
                                res.push(i);
                                res.push(x / i);
                            }
                        }
                    }
                }
                res.sort();

                if res.len() > 0 {
                    return Ok(Some(res));
                }

                Ok(Some(res))
            }

            // Factorization implement, using Pollard-Rho Algorithm
            fn factorize(&self) -> Result<Vec::<Self>, ArithmeticError> {
                // TODO: implmented trial division instead for now
                let mut x: $t = *self;
                let mut res: Vec::<Self> = vec![];

                for i in 2..=x.sqrt() {
                    while x % i == 0 {
                        res.push(i);
                        x /= i;
                    }
                }
                if x > 1 {
                    res.push(x);
                }
                res.sort();

                Ok(res)
            }

            // Modular multiplication implementation
            fn modular_mul(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError> {
                // all arguments will be casted internally into u128 to avoid overflow
                let mut res: u128 = match *modulus != 0 {
                    true => 0,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    }
                };

                let mut x: u128 = *self as u128;
                let mut y: u128 = *other as u128;
                let m: u128 = *modulus as u128;

                while y != 0 {
                    if y & 1 == 1 {
                        res = match res.checked_add(x) {
                            Some(n) => n % m,
                            None => {
                                return Err(ArithmeticError {
                                    kind: ArithmeticErrorKind::OVERFLOW,
                                })
                            }
                        };
                    }

                    x = match x.checked_mul(2) {
                        Some(n) => n % m,
                        None => {
                            return Err(ArithmeticError {
                                kind: ArithmeticErrorKind::OVERFLOW,
                            })
                        }
                    };
                    y >>= 1;
                }

                // shrink result into return type
                Ok(res as $t)
            }

            // Modular exponentiation implementation, using Binary Exponentiation Algorithm
            fn modular_pow(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError> {
                // all arguments will be casted internally into u128 to avoid overflow
                let mut res: u128 = match *modulus != 0 {
                    true => 1,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    }
                };

                let mut x = *self as u128;
                let mut y = *other as u128;
                let m = *modulus as u128;
                x %= m;

                while y != 0 {
                    if y & 1 == 1 {
                        res = match res.checked_mul(x) {
                            Some(n) => n % m,
                            None => {
                                return Err(ArithmeticError {
                                    kind: ArithmeticErrorKind::OVERFLOW,
                                })
                            }
                        };
                    }

                    x = match x.checked_mul(x) {
                        Some(n) => n % m,
                        None => {
                            return Err(ArithmeticError {
                                kind: ArithmeticErrorKind::OVERFLOW,
                            })
                        }
                    };
                    y >>= 1;
                }

                // shrink result into return type
                Ok(res as $t)
            }

            fn is_prime(&self) -> Result<bool, ArithmeticError> {
                let n = *self;

                if n == 2 || n == 3 || n == 5 || n == 7 {
                    return Ok(true);
                }
                if n % 2 == 0 || n % 3 == 0 || n % 5 == 0 || n % 7 == 0 {
                    return Ok(false);
                }
                if n < 121 {
                    return Ok(n > 1);
                }

                // finding d, s that satisfies n = d * 2^s
                let bin_expan = |n: u128| {
                    let mut d = n;
                    let mut s = 0;
                    while (d & 1) == 0 {
                        s += 1;
                        d >>= 1;
                    }
                    (d, s)
                };

                // Michal Forisek's Algorithm for 32-bit integer
                let _is_prime32 = |n: $t| {
                    let base: Vec<u128> = vec![
                        0x3ce7, 0x7e2, 0xa6, 0x1d05, 0x1f80, 0x3ead, 0x2907, 0x112f, 0x79d, 0x50f, 0xad8, 0xe24,
                        0x230, 0xc38, 0x145c, 0xa61, 0x8fc, 0x7e5, 0x122c, 0x5bf, 0x2478, 0xfb2, 0x95e, 0x4fee,
                        0x2825, 0x1f5c, 0x8a5, 0x184b, 0x26c, 0xeb3, 0x12f4, 0x1394, 0xc71, 0x535, 0x1853, 0x14b2,
                        0x432, 0x957, 0x13f9, 0x1b95, 0x323, 0x4f5, 0xf23, 0x1a6, 0x2ef, 0x244, 0x1279, 0x27ff,
                        0x2ea, 0xb87, 0x22c, 0x89e, 0xec2, 0x1e1, 0x5f2, 0xd94, 0x1e1, 0x9b7, 0xcc2, 0x1601, 0x1e8,
                        0xd2d, 0x1929, 0xd10, 0x11, 0x3b01, 0x5d2, 0x103a, 0x7f4, 0x75a, 0x715, 0x1d3, 0xceb,
                        0x36da, 0x18e3, 0x292, 0x3ed, 0x387, 0x2e1, 0x75f, 0x1d17, 0x760, 0xb20, 0x6f8, 0x1d87,
                        0xd48, 0x3b7, 0x3691, 0x10d0, 0xb1, 0x29, 0x4da3, 0xc26, 0x33a5, 0x2216, 0x23b, 0x1b83,
                        0x1b1f, 0x4af, 0x160, 0x1923, 0xa5, 0x491, 0xcf3, 0x3d2, 0xe9, 0xbbb, 0xa02, 0xbb2, 0x295b,
                        0x272e, 0x949, 0x76e, 0x14ea, 0x115f, 0x613, 0x107, 0x6993, 0x8eb, 0x131, 0x29d, 0x778,
                        0x259, 0x182a, 0x1ad, 0x78a, 0x3a19, 0x6f8, 0x67d, 0x20c, 0xdf9, 0xec, 0x938, 0x1802,
                        0xb22, 0xd955, 0x6d9, 0x1052, 0x2112, 0xde, 0xa13, 0xab7, 0x7ef, 0x8b2, 0x8e4, 0x176,
                        0x854, 0x32d, 0x5cec, 0x64a, 0x1146, 0x1427, 0x6bd, 0xe0d, 0xd26, 0x3800, 0x243, 0xa5,
                        0x55f, 0x2722, 0x3148, 0x2658, 0x55b, 0x218, 0x74b, 0x2a70, 0x359, 0x89e, 0x169c, 0x1b2,
                        0x1f95, 0x44d2, 0x2d7, 0xe37, 0x63b, 0x1350, 0x851, 0x7ed, 0x2003, 0x2098, 0x1858, 0x23df,
                        0x1fbe, 0x74e, 0xce0, 0x1d1f, 0x22f3, 0x61b9, 0x21d, 0x4aab, 0x170, 0x236, 0x162a, 0x19b,
                        0x20a, 0x403, 0x2017, 0x802, 0x1990, 0x2741, 0x266, 0x306, 0x91d, 0xbbf, 0x8981, 0x1262,
                        0x480, 0x6f9, 0x404, 0x604, 0xe9f, 0x1ed, 0x117a, 0x9d9, 0x68dd, 0x20a2, 0x360, 0x49e3,
                        0x1559, 0x98f, 0x2a, 0x119f, 0x67c, 0xa6, 0x4e1, 0x1873, 0x9f9, 0x130, 0x110, 0x1c76, 0x49,
                        0x199a, 0x383, 0xb00, 0x144d, 0x3412, 0x1b8e, 0xb02, 0xc7f, 0x32b, 0x39a, 0x15e, 0x1d5a,
                        0x1164, 0xd79, 0xa67, 0x1264, 0x1a2, 0x655, 0x493, 0xd8f, 0x58, 0x2c51, 0x19c, 0x617, 0xc2,
                    ];

                    let is_sprp = |n: u128, a: u128| {
                        let (d, s) = bin_expan(n - 1);
                        let mut x = a.modular_pow(&d, &n).unwrap();
                        if x == 1 {
                            return true;
                        }
                        for _ in 0..s {
                            if x == n - 1 {
                                return true;
                            }
                            x = x.modular_pow(&2, &n).unwrap();
                        }
                        false
                    };

                    // all variables must be u128 to handle operation below
                    let mut h = n as u128;
                    h = ((h >> 16) ^ h) * 0x45d9f3b;
                    h = ((h >> 16) ^ h) * 0x45d9f3b;
                    h = ((h >> 16) ^ h) & 255;

                    is_sprp(n as u128, base[h as usize])
                };

                // Miller-Rabin Algorithm for 64-bit integer
                let _is_prime64 = |n: $t| {
                    let f = |n: u128, a: u128| {
                        if n == a {
                            return true;
                        }
                        let (d, s) = bin_expan(n - 1);
                        let mut x = a.modular_pow(&d, &n).unwrap();
                        if x == 1 {
                            return true;
                        }
                        for _ in 0..s {
                            if x == n - 1 {
                                return true;
                            }
                            x = x.modular_pow(&2, &n).unwrap();
                        }
                        false
                    };

                    let base64: Vec<u128> = vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

                    for a in base64 {
                        if !f(n as u128, a) {
                            return false;
                        }
                    }
                    true
                };

                // Iterative Miller-Rabin Algorithm for 128-bit integer
                let _is_prime128 = |n: $t, iter: usize | {
                    let f = |n: u128, a: u128| {
                        let (d, s) = bin_expan(n - 1);
                        let mut x = a.modular_pow(&d, &n).unwrap();
                        if x == 1 {
                            return true;
                        }
                        for _ in 0..s {
                            if x == n - 1 {
                                return true;
                            }
                            x = x.modular_pow(&2, &n).unwrap();
                        }
                        false
                    };

                    for _ in 0..iter {
                        // pick an random integer between [2, n - 2]
                        let a = 2 + random::<u128>() % (n - 4) as u128;
                        if !f(n as u128, a) {
                            return false;
                        }
                    }
                    true
                };

                let sz = mem::size_of::<$t>();

                if sz <= 4 {
                    // test for 32-bit size integers
                    // works deterministically
                    Ok(_is_prime32(n))
                } else if 4 < sz && sz <= 8 {
                    // test for 64-bit size integers
                    // works deterministically
                    Ok(_is_prime64(n))
                } else {
                    // test for 128-bit size integers, probabilistic
                    // probobility of returning true for pseudoprime
                    // is approximate to 0.25^20 * ln(n)
                    Ok(_is_prime128(n, 20))
                }
            }

            fn modular_sqrt(&self, modulus: &Self) -> Result<Self, ArithmeticError> {
                unimplemented!()
            }

            fn pi(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            fn euler_phi(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            fn tau(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            fn sigma(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            fn omega(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            fn jacobi(&self) -> Result<isize, ArithmeticError> {
                unimplemented!()
            }
        }

        #[cfg(test)]
        mod $test_mod {
            #[test]
            fn test_gcd() {
                todo!()
            }

            #[test]
            fn test_ext_gcd() {
                todo!()
            }

            #[test]
            fn test_factorize() {
                todo!()
            }

            #[test]
            fn test_modular_mul() {
                todo!()
            }

            #[test]
            fn test_modular_pow() {
                todo!()
            }
        }
    )+};
}

impl_int_isize!(isize, test_isize;
                i32, test_i32;
                i64, test_i64;
                i128, test_i128);

impl_int_usize!(usize, test_usize;
                u32, test_u32;
                u64, test_u64;
                u128, test_u128);
