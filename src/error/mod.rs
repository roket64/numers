use std::error::Error;
use std::fmt::{Debug, Display, Formatter};

pub enum ArithmeticErrorKind {
    Overflow,
    DivideByZero,
}
pub enum CipherErrorKind {}
pub enum CongrErrorKind {
    NoSuchSolution,
}

pub struct ArithmeticError {
    pub kind: ArithmeticErrorKind,
}

pub struct CipherError {
    pub kind: CipherErrorKind,
}

pub struct CongruenceError {
    pub kind: CongrErrorKind,
}

macro_rules! impl_errorkind {
    ($($err_kind: ident),+) => {$(
        impl Debug for $err_kind {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(f, "")
            }
        }

        impl Display for $err_kind {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(f, "")
            }
        }
    )+};
}

macro_rules! impl_errorname {
    ($($err_name: ident), +) => {$(
        impl Error for $err_name {
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

macro_rules! impl_test {
    ($($errkind: ident; $errname: ident), +) => {$(
        impl Debug for $errkind {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(f, "")
            }
        }

        impl Display for $errkind {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(f, "")
            }
        }

        // impl Error for $errname {
        //     fn cause(&self) -> Option<&dyn Error> {
        //     }

        //     fn description(&self) -> &str {
        //     }

        //     fn source(&self) -> Option<&(dyn Error + 'static)> {
        //     }
        // }
    )+};
}

impl_test!(ArithmeticErrorKind; ArithmeticError);
// impl_errorkind!(ArithmeticErrorKind, CongrErrorKind, CipherErrorKind);