use std::error::Error;
use std::fmt::{Debug, Display};

pub enum ArithmeticErrorKind {}
pub enum CongrErrorKind{}

pub struct ArithmeticError {
    pub kind: ArithmeticErrorKind,
}

pub struct CongruenceError {
    pub kind: CongrErrorKind,
}
