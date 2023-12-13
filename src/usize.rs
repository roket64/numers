use std::mem;

use num_integer::Roots;
use rand::random;

use crate::error::{ArithmeticError, ArithmeticErrorKind};
use crate::BezoutIdentity;
use crate::Int;

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

                let mut s = (1, 0);
                let mut t = (0, 1);
                let mut r = (*self, *other);

                while r.0 != 0 {
                    let q = r.1 / r.0;
                    let f = |mut r: (Self, Self)| {
                        mem::swap(&mut r.0, &mut r.1);
                        r.0 = r.0 - q * r.1;
                        r
                    };
                    r = f(r);
                    s = f(s);
                    t = f(t);
                }

                Ok(BezoutIdentity {
                    gcd: r.1 as $t,
                    a_coeff: s.1 as i64,
                    b_coeff: t.1 as i64,
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
                    Ok(Some(res))
                } else {
                    Ok(None)
                }
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

            // Modualr addition implementation
            fn modular_add(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError> {
                let mut x = *self;
                let mut y = *other;
                let m = match *modulus != 0 {
                    true => *modulus,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    },
                };
                // (a + b) (mod m) = ((a (mod m)) + (b (mod m))) (mod m)
                x %= m;
                y %= m;

                if x >= m - y {
                    Ok(x - (m - y))
                } else {
                    Ok(x + y)
                }
            }

            // Modular multiplication implementation
            fn modular_mul(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError> {
                let mut res = match *modulus != 0 {
                    true => 0,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    }
                };

                let mut x = *self;
                let mut y = *other;
                let m = *modulus;
                // (a * b) (mod m) = ((a (mod m)) * (b (mod m))) (mod m)
                x %= m;
                y %= m;

                while y != 0 {
                    if y & 1 == 1 {
                        res = res.modular_add(&x, &m)?;
                    }
                    x = res.modular_add(&x, &m)?;
                    y >>= 1;
                }

                Ok(res)
            }

            // Modular exponentiation implementation, using Binary Exponentiation Algorithm
            fn modular_pow(&self, exponent: &Self, modulus: &Self) -> Result<Self, ArithmeticError> {
                let mut res = match *modulus != 0 {
                    true => 1,
                    false => {
                        return Err(ArithmeticError {
                            kind: ArithmeticErrorKind::ZERO
                        })
                    }
                };

                let mut x = *self;
                let mut y = *exponent;
                let m = *modulus;
                x %= m;

                while y != 0 {
                    if y & 1 == 1 {
                        res = res.modular_mul(&x, &m)?;
                    }
                    x = x.modular_mul(&y, &m)?;
                    y >>= 1;
                }

                Ok(res)
            }

            fn is_prime(&self) -> Result<bool, ArithmeticError> {
                let n = *self;

                // do some cheap checks
                if n == 2 || n == 3 || n == 5 || n == 7 {
                    return Ok(true);
                }
                if n % 2 == 0 || n % 3 == 0 || n % 5 == 0 || n % 7 == 0 {
                    return Ok(false);
                }

                // finding d, s such that n = d * 2^s
                let bin_expan = |n: $t| {
                    let mut d = n;
                    let mut s = 0;
                    while (d & 1) == 0 {
                        s += 1;
                        d >>= 1;
                    }
                    (d, s)
                };

                let checker = |n: $t, a: $t| {
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

                let _is_prime32 = |n: $t| {
                    let base32 = vec![2, 7, 61];
                    for a in base32 {
                        if !checker(n , a) {
                            return false;
                        }
                    }
                    true
                };

                let _is_prime64 = |n: $t| {
                    let base64 = vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
                    for a in base64 {
                        if !checker(n, a) {
                            return false;
                        }
                    }
                    true
                };

                // Iterative Miller-Rabin Algorithm for 128-bit integer
                let _is_prime128 = |n: $t, iter: usize | {
                    for _ in 0..iter {
                        // pick a random integer between [2, n - 2]
                        let a = random::<$t>() % (n - 4) + 2;
                        if !checker(n, a) {
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

            // numbers of primes less or equal to an integer
            fn pi(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            // numbers of integers coprime to an integer
            fn euler_phi(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            // numbers of positive factors of an integer
            fn tau(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            // sum of positive divisors of an integer including trivial ones
            fn sigma(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            // number of prime factors of an integer
            fn omega(&self) -> Result<usize, ArithmeticError> {
                unimplemented!()
            }

            // jacobi symbol of an integer
            fn jacobi(&self) -> Result<isize, ArithmeticError> {
                unimplemented!()
            }
        }

        #[cfg(test)]
        mod $test_mod {
            #[test]
            fn test_ext_gcd() {
                todo!()
            }

            #[test]
            fn test_factorize() {
                todo!()
            }

            #[test]
            fn test_modular_add() {
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

            #[test]
            fn modular_sqrt() {
                todo!()
            }

            #[test]
            fn is_prime() {
                todo!()
            }

            #[test]
            fn test_pi() {
                unimplemented!()
            }

            #[test]
            fn tset_euler_phi() {
                unimplemented!()
            }

            #[test]
            fn test_tau() {
                unimplemented!()
            }

            #[test]
            fn test_sigma() {
                unimplemented!()
            }

            #[test]
            fn test_omega() {
                unimplemented!()
            }

            #[test]
            fn test_jacobi() {
                unimplemented!()
            }
        }
    )+};
}

impl_int_usize!(usize, test_usize;
                u32, test_u32;
                u64, test_u64;
                u128, test_u128);
