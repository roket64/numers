use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result};

pub struct IntegerError {
    pub kind: IntegerErrorKind,
}

pub struct ArithmeticError {
    pub kind: ArithmeticErrorKind,
}

pub struct LogicError {
    pub kind: LogicErrorKind,
}

pub enum IntegerErrorKind {
    ARITHMETIC(ArithmeticError),
    LOGIC(LogicError),
}

impl Display for IntegerErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::ARITHMETIC(err) => write!(f, "{}", err),
            Self::LOGIC(err) => write!(f, "{}", err),
        }
    }
}

pub enum ArithmeticErrorKind {
    OVERFLOW,
    ZERO,
}

impl Display for ArithmeticErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let kind = match self {
            Self::OVERFLOW => {
                "ArithmeticErrorKind::OVERFLOW: An overflow occurred while performing arithmetic operations."
            }
            Self::ZERO => {
                "ArithmeticErrorKind::ZERO: Found illegal zero for non-zero values."
            }
        };
        write!(f, "{}", kind)
    }
}

pub enum LogicErrorKind {
    UNSOLVABLE,
}

impl Display for LogicErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let kind = match self {
            Self::UNSOLVABLE => {
                "LogicErrorKind::UNSOLVABLE: Could not find any possible solution of given equation."
            }
        };
        write!(f, "{}", kind)
    }
}

macro_rules! impl_error {
    ($($err: ident),+) => {$(
        impl Display for $err {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result {
                write!(f, "{}", self.kind)
            }
        }

        impl Debug for $err {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result {
                write!(f, "{}", self.kind)
            }
        }

        impl Error for $err {
            fn cause(&self) -> Option<&dyn Error> {
                None
            }

            fn description(&self) -> &str {
                "description is deprecated; use Display"
            }

            fn source(&self) -> Option<&(dyn Error + 'static)> {
                None
            }
        }
    )+};
}

impl_error!(IntegerError, ArithmeticError, LogicError);