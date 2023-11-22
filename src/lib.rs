// Copyright (c) 2023 roket64.
// Licensed under the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>.
// This file may not be copied, modified, or distributed
// except according to those terms.

use num::integer::Integer;
use num::integer::Roots;
use std::mem;
use std::vec::Vec;

use error::{ArithmeticError, ArithmeticErrorKind};
use solver::BezoutIdentity;

pub trait Int: Integer {
    /// Calculates greatest common divisor of given integeres.
    fn igcd(&self, other: &Self) -> Result<Self, ArithmeticError>;

    /// Calculates greatest common divisor of given integers and returns the BézoutIdentity,
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
    /// # Examples
    /// ```
    /// let n: i32 = 2;
    /// let m: i32 = 3;
    /// let k: i32 = 4;
    /// assert_eq!(modular_pow(n, m, k).unwrap(), 0);
    /// ```
    fn modular_pow(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError>;

    /// Tests primality of the given intger and returns `bool` wether integer is prime. \
    /// Time complexity is `O(log^3N)`, since it's a variant of Miller-Rabin Test.
    /// # Examples
    /// ```
    /// let n: i32 = 2;
    /// let m: i32 = 16;k
    /// assert!(n.is_prime());
    /// assert!(!m.is_prime());
    /// ```
    fn is_prime(&self) -> Result<bool, ArithmeticError>;
}

/// Calculates Greatest Common Divisor
pub fn gcd<T: Int>(x: T, y: T) -> Result<T, ArithmeticError> {
    x.igcd(&y)
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

macro_rules! impl_int_isize {
    ($($t: ty, $test_mod: ident);+) => {$(
        impl Int for $t {
            fn igcd(&self, other: &Self) -> Result<Self, ArithmeticError>{
                // converting to absolute value may cause overflow
                let mut x: $t = match self.checked_abs() {
                    Some(n) => n,
                    None => return Err(ArithmeticError{
                        kind: ArithmeticErrorKind::OVERFLOW
                    }),
                };
                let mut y: $t = match other.checked_abs() {
                    Some(n) => n,
                    None => return Err(ArithmeticError{
                        kind: ArithmeticErrorKind::OVERFLOW
                    }),
                };

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

                while y != 0 {
                    // Removing factors of two in x and y.
                    while (x & 1) == 0 {
                        x >>= 1;
                    }
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
                // use checked_rem_euclid()
                let mut res: $t = match *modulus != 0 {
                    true => 0,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    }
                };

                let mut x: $t = *self;
                let mut y: $t = match *other < 0 {
                    true => -*other,
                    false => *other,
                };
                let m: $t = *modulus;

                while y != 0 {
                    if y & 1 == 1 {
                        res = match res.checked_add(x) {
                            Some(n) => n,
                            None => {
                                return Err(ArithmeticError {
                                    kind: ArithmeticErrorKind::OVERFLOW,
                                })
                            }
                        };
                        // using rem_euclid() since we want a nonnegative remainder
                        res = res.rem_euclid(m);
                    }

                    x = match x.checked_mul(2) {
                        Some(n) => n,
                        None => {
                            return Err(ArithmeticError {
                                kind: ArithmeticErrorKind::OVERFLOW,
                            })
                        }
                    };
                    res = res.rem_euclid(m);
                    y >>= 1;
                }

                Ok(res)
            }

            fn modular_pow(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError> {
                let mut res: $t = match *modulus != 0 {
                    true => 1,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    }
                };

                let mut x: $t= *self;
                let mut y: $t = match *other < 0 {
                    true => *other,
                    false => return Ok(0),
                };
                let m: $t = *modulus;

                x %= m;

                while y != 0 {
                    if y & 1 == 1 {
                        res = match res.checked_mul(x) {
                            Some(n) => n,
                            None => {
                                return Err(ArithmeticError {
                                    kind: ArithmeticErrorKind::OVERFLOW,
                                })
                            }
                        };
                        x = x.rem_euclid(m);
                    }

                    x = match x.checked_mul(x) {
                        Some(n) => n,
                        None => {
                            return Err(ArithmeticError {
                                kind: ArithmeticErrorKind::OVERFLOW,
                            })
                        }
                    };
                    x = x.rem_euclid(m);
                    y >>= 1;
                }

                Ok(x)
            }

            fn is_prime(&self) -> Result<bool, ArithmeticError> {
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
            // GCD implmentation, using Binary Euclid Algorithm
            fn igcd(&self, other: &Self) -> Result<Self, ArithmeticError> {
                // It's not necessary to cast them into absoulute value,
                // since this is implementation for usize values.
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

                while y != 0 {
                    // Removing factors of two in x and y.
                    while (x & 1) == 0 {
                        x >>= 1;
                    }
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
                let mut res: $t = match *modulus != 0 {
                    true => 0,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    }
                };

                let mut x: $t = *self;
                let mut y: $t = *other;
                let m: $t = *modulus;

                while y != 0 {
                    if y & 1 == 1 {
                        res = match res.checked_add(x) {
                            Some(n) => n,
                            None => {
                                return Err(ArithmeticError {
                                    kind: ArithmeticErrorKind::OVERFLOW,
                                })
                            }
                        };
                        // No need to use `checked_rem_euclid()`
                        // since x and m are always positive
                        res %= m;
                    }

                    x = match x.checked_mul(2) {
                        Some(n) => n,
                        None => {
                            return Err(ArithmeticError {
                                kind: ArithmeticErrorKind::OVERFLOW,
                            })
                        }
                    };
                    // No need to use `checked_rem_euclid()`
                    // since x and m are always positive
                    x %= m;
                    y >>= 1;
                }

                Ok(res)
            }

            // Modular exponentiation implementation, using Binary Exponentiation Algorithm
            fn modular_pow(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError> {
                let mut res: $t = match *modulus != 0 {
                    true => 1,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    }
                };

                let mut x: $t= *self;
                let mut y: $t = *other;
                let m: $t = *modulus;

                x %= m;

                while y != 0 {
                    if y & 1 == 1 {
                        res = match res.checked_mul(x) {
                            Some(n) => n,
                            None => {
                                return Err(ArithmeticError {
                                    kind: ArithmeticErrorKind::OVERFLOW,
                                })
                            }
                        };
                        // No need to use `checked_rem_euclid()`
                        // since x and m are always positive
                        x %= m;
                    }

                    x = match x.checked_mul(x) {
                        Some(n) => n,
                        None => {
                            return Err(ArithmeticError {
                                kind: ArithmeticErrorKind::OVERFLOW,
                            })
                        }
                    };
                    // No need to use `checked_rem_euclid()`
                    // since x and m are always positive
                    x %= m;
                    y >>= 1;
                }

                Ok(x)
            }

            fn is_prime(&self) -> Result<bool, ArithmeticError> {
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
                i64, test_i64);

impl_int_usize!(usize, test_usize;
                u32, test_u32;
                u64, test_u64);

pub mod cipher;
pub mod error;
pub mod solver;
