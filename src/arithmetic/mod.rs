use std::num::IntErrorKind;

pub trait Int: Sized + PartialOrd + Ord + PartialEq + Eq {
    fn modulo(&self, modulo: &Self) -> Result<Self, Box<IntErrorKind>>;
    fn modular_mul(&self, other: &Self, modulo: &Self) -> Result<Self, Box<IntErrorKind>>;
    fn modular_pow(&self, other: &Self, modulo: &Self) -> Result<Self, Box<IntErrorKind>>;
}

/// Calculates least positive integer k such that `x = (y * k) + modulo.`
/// # Example
/// ```
/// assert_eq!(modulo(9, 3).uwnrp(), 0);
/// assert_eq!(modulo(-9, 4).unwrap(), 3);
/// assert_eq!(modulo(-9, -4).unwrap(), 3);
/// ```
pub fn modulo<T: Int>(x: T, modulo: T) -> Result<T, Box<IntErrorKind>> {
    x.modulo(&modulo)
}

/// Calculates least positive integer from modular multiplication between Int types
/// and returns `Result<T, Box<IntErrorKind>>` wether the computation was successful.
/// # Examples
/// ```
/// let n: i32 = 5;
/// let m: i32 = 10;
/// let k: i32 = 7;
/// assert_eq!(modular_mul(n, m, k).unwrap(), 1);
/// ```
pub fn modular_mul<T: Int>(x: T, y: T, modulo: T) -> Result<T, Box<IntErrorKind>> {
    x.modular_mul(&y, &modulo)
}

/// Calculates least positive ineger from modular exponentiation between Int types
/// and returns `Result<T, Box<IntErrorKind>>` wether the compute was successful.
/// # Examples
/// ```
/// let n: i32 = 2;
/// let m: i32 = 3;
/// let k: i32 = 4;
/// assert_eq!(modular_pow(n, m, k).unwrap(), 0);
/// ```
pub fn modular_pow<T: Int>(x: T, y: T, modulo: T) -> Result<T, Box<IntErrorKind>> {
    x.modular_pow(&y, &modulo)
}

macro_rules! impl_arithmetic_isize {
    ($($t: ty; $test_mod: ident), +) => {$(
        impl Int for $t {
            fn modulo(&self, modulo: &Self) -> Result<Self, Box<IntErrorKind>> {
                todo!();
            }

            fn modular_mul(&self, other: &Self, modulo: &Self) -> Result<Self, Box<IntErrorKind>> {
                // handling zero modulo
                let mut res: $t = match *modulo {
                    0 => return Err(Box::new(IntErrorKind::Zero)),
                    _ => 0,
                };

                let mut x = *self;

                let mut y = *other;

                // handling negative multiplier
                // let mut y = match (*other > 0) {
                //     true => *other,
                //     this will panic when the value of *other is $t::MIN
                //     false => -*other,
                // };

                if *modulo == 1 {
                    return Ok(0);
                }

                while y != 0 {
                    if y & 1 == 1 {
                        match res.checked_add(x) {
                            Some(n) => res = n % modulo,
                            None => match (x > 0 && y > 0) {
                                true => return Err(Box::new(IntErrorKind::PosOverflow)),
                                false => return Err(Box::new(IntErrorKind::NegOverflow)),
                            },
                        }
                    }
                    // this will return None when x > $t::MAX / 2
                    match x.checked_mul(2) {
                        Some(n) => x = n % modulo,
                        None => match (x > 0 && y > 0) {
                            true => return Err(Box::new(IntErrorKind::PosOverflow)),
                            false => return Err(Box::new(IntErrorKind::NegOverflow)),
                        },
                    }
                    y /= 2;
                    // use bitshift instead only if when you 
                    // have implemented the handling of negative multiplier
                    // y >>= 1;
                }

                // here, we have an integer such that
                // (modulo * k) + res = x * y
                // for some integer k, but since we need a least positive value...
                match (res >= 0) {
                    true => Ok(res),
                    false => Ok(res + *modulo),
                }
            }

            fn modular_pow(&self, other: &Self, modulo: &Self) -> Result<Self, Box<IntErrorKind>> {
                // handling zero modulo
                let mut res: $t = match *modulo {
                    0 => return Err(Box::new(IntErrorKind::Zero)),
                    _ => 1,
                };

                let mut x = *self % *modulo;

                // handling negative exponent
                let mut y = match (*other > 0) {
                    true => *other,
                    false => return Err(Box::new(IntErrorKind::NegOverflow)),
                };

                // handling when modulo is one
                if *modulo == 1 {
                    return Ok(0);
                }

                while y != 0 {
                    if y & 1 == 1 {
                        match res.checked_mul(x) {
                            Some(n) => res = n % modulo,
                            None => match (x > 0) {
                                true => return Err(Box::new(IntErrorKind::PosOverflow)),
                                false => return Err(Box::new(IntErrorKind::NegOverflow)),
                            },
                        }
                    }
                    match x.checked_mul(x) {
                        Some(n) => x = n % modulo,
                        None => match (x > 0) {
                            true => return Err(Box::new(IntErrorKind::PosOverflow)),
                            false => return Err(Box::new(IntErrorKind::NegOverflow)),
                        },
                    }
                    y >>= 1;
                }
                // Here, we have an integer such that
                // (modulo * k) + res = x ^ y
                // for some integer k, but since we need a least positive value...
                match (res >= 0) {
                    true => Ok(res),
                    false => Ok(res + *modulo),
                }
            }
        }

        #[cfg(test)]
        mod $test_mod {
            // use std::i32::MAX as I32_MAX;
            // use std::i64::MAX as I64_MAX;
            // use std::i32::MIN as I32_MIN;
            // use std::i64::MIN as I64_MIN;

            #[test]
            fn test_modular_mul() {
                use crate::arithmetic::modular_mul as _mulmod;

                fn test_mulmod_err() {
                    // divide by zero
                    assert!(_mulmod(2 as $t, 3 as $t, 0).is_err());

                    // will return error when x is greater than $t::MAX / 2
                    // assert!(_mulmod(I32_MAX as $t, I32_MAX as $t, 2).is_err());
                }

                fn test_mulmod_val() {
                    // 6 mod 4
                    assert_eq!(_mulmod(2 as $t, 3 as $t, 4 as $t).unwrap(), 2);
                    // 8 mod 4
                    assert_eq!(_mulmod(2 as $t, 4 as $t, 4 as $t).unwrap(), 0);

                    // -6 mod 4
                    assert_eq!(_mulmod(-2 as $t, 3 as $t, 4 as $t).unwrap(), 2);
                    assert_eq!(_mulmod(2 as $t, -3 as $t, 4 as $t).unwrap(), 2);

                    // -8 mod 4
                    assert_eq!(_mulmod(-2 as $t, 4 as $t, 4 as $t).unwrap(), 0);
                    assert_eq!(_mulmod(2 as $t, -4 as $t, 4 as $t).unwrap(), 0);

                    // -9 mod -4
                    // assert_eq!(_mulmod(-1 as $t, 9 as $t, -4 as $t).unwrap(), 1);
                }

                test_mulmod_err();
                test_mulmod_val();
            }

            #[test]
            fn test_modular_pow() {
                use crate::arithmetic::modular_pow as _powmod;

                fn test_powmod_err() {
                    // divide by zero
                    assert!(_powmod(2, 3, 0).is_err());
                    // negative exponent
                    assert!(_powmod(2, -3, 2).is_err());
                }

                fn test_powmod_val() {
                    // 8 mod 4
                    assert_eq!(_powmod(2 as $t, 3 as $t, 4 as $t).unwrap(), 0);
                    // 9 mod 4
                    assert_eq!(_powmod(3 as $t, 2 as $t, 4 as $t).unwrap(), 1);
                }

                test_powmod_err();
                test_powmod_val();
            }
        }
    )+};
}

macro_rules! impl_arithmetic_usize {
    ($($t: ty; $test_mod: ident), +) => {$(
        impl Int for $t {
            fn modulo(&self, modulo: &Self) -> Result<Self, Box<IntErrorKind>> {
                todo!();
            }

            fn modular_mul(&self, other: &Self, modulo: &Self) -> Result<Self, Box<IntErrorKind>> {
                // handling zero modulo
                let mut res: $t = match *modulo {
                    0 => return Err(Box::new(IntErrorKind::Zero)),
                    _ => 0,
                };
                let mut x = *self;
                let mut y = *other;

                if *modulo == 0 {
                    return Ok(0);
                }

                while y != 0 {
                    if y & 1 == 1 {
                        match res.checked_add(x) {
                            Some(n) => res = n % modulo,
                            None => return Err(Box::new(IntErrorKind::PosOverflow)),
                        }
                    }
                    match x.checked_mul(2) {
                        Some(n) => x = n % modulo,
                        None => return Err(Box::new(IntErrorKind::PosOverflow)),
                    }
                    y >>= 1;
                }

                // Since x and y are always positive, remainder will always be positive
                Ok(res)
            }

            fn modular_pow(&self, other: &Self, modulo: &Self) -> Result<Self, Box<IntErrorKind>> {
                // handling zero modulo
                let mut res: $t = match *modulo {
                    0 => return Err(Box::new(IntErrorKind::Zero)),
                    _ => 0,
                };
                let mut x = *self;
                let mut y = *other;

                if *modulo == 0 {
                    return Ok(0);
                }

                while y != 0 {
                    if y & 1 == 1 {
                        match res.checked_mul(x) {
                            Some(n) => res = n % modulo,
                            None => return Err(Box::new(IntErrorKind::PosOverflow)),
                        }
                    }
                    match x.checked_mul(x) {
                        Some(n) => x = n % modulo,
                        None => return Err(Box::new(IntErrorKind::NegOverflow)),
                    }
                    y >>= 1;
                }
                // Since x and y are always positive, remainder will always be positive
                Ok(res)
            }
        }

        #[cfg(test)]
        mod $test_mod {
            // use std::u32::MAX as U32_MAX;
            // use std::u64::MAX as U64_MAX;

            #[test]
            fn test_modular_mul() {
                use crate::arithmetic::modular_mul as _mulmod;

                fn test_mulmod_err() {
                    // divide by zero
                    assert!(_mulmod(2, 3, 0).is_err());
                }

                fn test_mulmod_val() {
                    // 6 mod 4
                    assert_eq!(_mulmod(2, 3, 4).unwrap(), 2);

                    // 8 mod 3
                    assert_eq!(_mulmod(2, 4, 3).unwrap(), 2);

                    // 316933 mod 97
                    assert_eq!(_mulmod(557, 569, 97).unwrap(), 34);

                    // 43521575 mod 8
                    assert_eq!(_mulmod(8704315, 5, 8).unwrap(), 7);
                }

                test_mulmod_err();
                test_mulmod_val();
            }

            #[test]
            fn test_modular_pow() {
                use crate::arithmetic::modular_pow as _powmod;

                fn test_powmod_err() {
                    // divide by zero
                    assert!(_powmod(2, 3, 0).is_err());
                }

                fn test_powmod_val() {
                    // 8 mod 3
                    assert_eq!(_powmod(2, 3, 3).unwrap(), 2);

                    // 9 mod 4
                    assert_eq!(_powmod(3, 2, 4).unwrap(), 1);
                    
                    // 2147483648
                    assert_eq!(_powmod(2, 32, 1usize << 32).unwrap(), 0);
                    // 1628413597910449 mod 37
                    assert_eq!(_powmod(49, 9, 37).unwrap(), 1);
                }

                test_powmod_err();
                test_powmod_val();
            }
        }
    )+};
}

impl_arithmetic_isize!(isize; test_isize, i32; test_i32, i64; test_i64);
impl_arithmetic_usize!(usize; test_usize, u32; test_u32, u64; test_u64);

mod error;