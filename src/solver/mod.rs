use super::Int;
use super::error::IntegerError;
use std::fmt::{Debug, Display};

pub trait Equation {
    fn solve(&self) -> Result<i32, IntegerError>;
}

pub struct Variable {
    val: char,
    exp: u32, // since we only interested in integer values
}

pub struct Term {
    coefficient: Option<i32>,
    variable: Option<Variable>,
    constant: Option<i32>,
}

/// Structure represents the Bézout's Identity. \
/// `a_coeff` represents `x` and `b_coeff` represents `y` from
/// equation `ax + by = gcd(a, b)`.
pub struct BezoutIdentity<T: Int> {
    pub gcd: T,
    pub a_coeff: T,
    pub b_coeff: T,
}

pub mod congr;
pub mod equation;
