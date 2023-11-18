use std::fmt::{Display, Formatter};

use super::error::LogicError;
use super::Int;

pub trait Equation {
    fn solve(&self) -> Result<i32, LogicError>;
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
#[derive(Debug)]
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

pub mod congr;
pub mod equation;
