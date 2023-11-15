// Copyright (c) 2023 roket64.
// Licensed under the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>.
// This file may not be copied, modified, or distributed
// except according to those terms.

use std::vec::Vec;
use std::mem;

use error::IntegerError;
use solver::BezoutIdentity;

pub trait Int: Sized + PartialOrd + Ord + PartialEq + Eq {
    fn gcd(&self, other: &Self) -> Result<Self, IntegerError>;
    fn ext_gcd(&self, other: &Self) -> Result<BezoutIdentity<Self>, IntegerError>;
    fn factorize(&self) -> Result<Vec<Self>, IntegerError>;
    fn modular_mul(&self, other: &Self, modulus: &Self) -> Result<Self, IntegerError>;
    fn modular_pow(&self, other: &Self, modulus: &Self) -> Result<Self, IntegerError>;
}

pub trait Equation {
    fn solve();
}

/// Calculates greatest common divisor of given integeres.
pub fn gcd<T: Int>(x: T, y: T) -> Result<T, IntegerError> {
    x.gcd(&y)
}

/// Calculates greatest common divisor of given integers and returns the BezoutIdentity,
/// which is the solution to the equation `ax + by = gcd(a, b)`.
pub fn ext_gcd<T: Int>(x: T, y: T) -> Result<BezoutIdentity<T>, IntegerError> {
    x.ext_gcd(&y)
}

/// Factorizes an single integer and returns `Vec` containing non-trivial divisors. \
/// Time complexity is O(n^¼), since it is a variant implementation of Pollard-rho algorithm.
pub fn factorize<T: Int>(x: T) -> Result<Vec<T>, IntegerError> {
    x.factorize()
}

/// Calculates least positive integer from modular multiplication between Int types
/// and returns `Result<T, IntegerError>` wether the computation was successful.
/// # Examples
/// ```
/// let n: i32 = 5;
/// let m: i32 = 10;
/// let k: i32 = 7;
/// assert_eq!(modular_mul(n, m, k).unwrap(), 1);
/// ```
pub fn modular_mul<T: Int>(x: T, y: T, modulus: T) -> Result<T, IntegerError> {
    x.modular_mul(&y, &modulus)
}

/// Calculates least positive ineger from modular exponentiation between Int types
/// and returns `Result<T, IntegerError>` wether the compute was successful.
/// # Examples
/// ```
/// let n: i32 = 2;
/// let m: i32 = 3;
/// let k: i32 = 4;
/// assert_eq!(modular_pow(n, m, k).unwrap(), 0);
/// ```
pub fn modular_pow<T: Int>(base: T, exponent: T, modulus: T) -> Result<T, IntegerError> {
    base.modular_pow(&exponent, &modulus)
}

macro_rules! impl_int_usize {
    ($($t: ty, $test_mod: ident);+) => {$(
        impl Int for $t {
            // GCD implmentation, using Binary Euclid Algorithm.
            fn gcd(&self, other: &Self) -> Result<Self, IntegerError> {
                // Since this is implementation for usize values,
                // it's not necessary to cast them into absoulute value.
                let mut x = *self;
                let mut y = *other;

                if x == 0 {
                    return Ok(y);
                }
                if y == 0 {
                    return Ok(x);
                }

                // Greatest power of two that divides both x and y.
                let mut k = 0;

                // Finding k by dividing x and y until one becomes an odd.
                while ((x | y) & 1) == 0 {
                    x >>= 1;
                    y >>= 1;
                    k += 1;
                }

                // Dividing x until it becomes an odd.
                while (x & 1) == 0 {
                    x >>= 1;
                }

                while y != 0 {
                    // Removing factors of two in y.
                    while (y & 1) == 0 {
                        y >>= 1;
                    }

                    // From here x always smaller or equal to y.
                    if x > y {
                        mem::swap(&mut x, &mut y);
                    }

                    y -= x;
                }

                // Restore common factors of two.
                Ok(x << k)
            }

            // Extended Euclidean Algorithm implementation
            fn ext_gcd(&self, other: &Self) -> Result<BezoutIdentity<Self>, IntegerError> {
                let mut a1 = *self;
                let mut b1 = *other;

                let mut x0 = 1;
                let mut x1 = 0;
                let mut y0 = 0;
                let mut y1 = 1;
        
        
                while b1 != 0 {
                    let q = a1 / b1;
                    (x0, x1) = (x1, x0 - q * x1);
                    (y0, y1) = (y1, y0 - q * y1);
                    (a1, b1) = (b1, a1 - q * b1);
                }
        
                Ok(BezoutIdentity {
                    gcd: a1,
                    a_coeff: x0,
                    b_coeff: y0,
                })
            }

            fn factorize(&self) -> Result<Vec::<Self>, IntegerError> {
                unimplemented!()
            }

            fn modular_mul(&self, other: &Self, modulus: &Self) -> Result<Self, IntegerError> {
                unimplemented!()
            }

            fn modular_pow(&self, other: &Self, modulus: &Self) -> Result<Self, IntegerError> {
                let mut res: $t = 1;
                let mut x: $t = *self;
                let mut y: $t = *other;
                let m = *modulus;

                x %= m;

                while y != 0 {
                    if y & 1 == 1 {
                        res = match res.checked_mul(x) {
                            Some(n) => n % m,
                            None => unimplemented!(),
                        };
                    }
                    x = match x.checked_mul(x) {
                        Some(n) => n % m,
                        None => unimplemented!(),
                    };
                    y >>= 1;
                }

                Ok(x)
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

impl_int_usize!(usize, test_usize;
                u32, test_u32;
                u64, test_u64);

pub mod cipher;
pub mod error;
pub mod solver;

mod tests;
