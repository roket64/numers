// Copyright (c) 2023 roket64.
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

pub mod constant;
pub mod error;
pub mod isize;
pub mod usize;

use std::fmt::{Display, Formatter};

use num_integer::Integer;

use error::ArithmeticError;

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

    /// Calculates least nonnegative integer from modular addition between given integers
    /// and returns `Result<T, ArithmeticError>` wether the caculation was successsful.
    fn modular_add(&self, other: &Self, modulus: &Self) -> Result<Self, ArithmeticError>;

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

pub fn modular_sqrt<T: Int>(x: T, modulus: T) -> Result<T, ArithmeticError> {
    x.modular_sqrt(&modulus)
}

/// returns the number of primes smaller or equal to `&self`
pub fn pi<T: Int>(x: T) -> Result<usize, ArithmeticError> {
    x.pi()
}

/// returns the number of integers that is coprime to `&self`
pub fn euler_phi<T: Int>(x: T) -> Result<usize, ArithmeticError> {
    x.euler_phi()
}

/// returns the number of positive factors of `&self`
pub fn tau<T: Int>(x: T) -> Result<usize, ArithmeticError> {
    x.tau()
}

/// returns the sum of positive divisors of `&self`, including trivial ones
pub fn sigma<T: Int>(x: T) -> Result<usize, ArithmeticError> {
    x.sigma()
}

/// returns the number of prime factors of `&self`
pub fn omega<T: Int>(x: T) -> Result<usize, ArithmeticError> {
    x.omega()
}

/// returns the Jacobi Symbol of the given integer.
pub fn jacobi<T: Int>(x: T) -> Result<isize, ArithmeticError> {
    x.jacobi()
}