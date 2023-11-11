use core::fmt::{self, Debug, Display};
use std::{error::Error, fmt::write};

pub enum ArithmeticErrorkind {
    DivideByZero,
    InvalidSolution,
}

impl Debug for ArithmeticErrorkind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "")
    }
}

impl Display for ArithmeticErrorkind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "")
    }
}

impl ArithmeticErrorkind {
    fn message(&self) -> &str {
        match self {
            Self::DivideByZero => "Unable to divide by zero.",
            Self::InvalidSolution => "Can not find valid solution.",
        }
    }
}

pub struct ArithmeticError {
    kind: ArithmeticErrorkind,
}

impl Debug for ArithmeticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "")
    }
}

impl Display for ArithmeticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "")
    }
}

impl Error for ArithmeticError {
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
