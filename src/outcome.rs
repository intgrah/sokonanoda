use std::any::Any;
use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub struct Rejection(pub String);

impl fmt::Display for Rejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "rejected: {}", self.0)
    }
}

impl Error for Rejection {}

#[derive(Debug)]
pub struct Decline(pub String);

impl fmt::Display for Decline {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "declined: {}", self.0)
    }
}

impl Error for Decline {}

pub enum CheckError {
    Rejected(Rejection),
    Declined(Decline),
    Internal(Box<dyn Any + Send>),
}

impl CheckError {
    pub(crate) fn from_panic(payload: Box<dyn Any + Send>) -> Self {
        match payload.downcast::<Rejection>() {
            Ok(r) => CheckError::Rejected(*r),
            Err(payload) => match payload.downcast::<Decline>() {
                Ok(d) => CheckError::Declined(*d),
                Err(payload) => CheckError::Internal(payload),
            },
        }
    }
}

impl fmt::Debug for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CheckError::Rejected(r) => f.debug_tuple("Rejected").field(r).finish(),
            CheckError::Declined(d) => f.debug_tuple("Declined").field(d).finish(),
            CheckError::Internal(_) => f.write_str("Internal(..)"),
        }
    }
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CheckError::Rejected(r) => r.fmt(f),
            CheckError::Declined(d) => d.fmt(f),
            CheckError::Internal(_) => f.write_str("internal error"),
        }
    }
}

impl Error for CheckError {}

pub(crate) fn decline<A>(msg: impl Into<String>) -> Result<A, Box<dyn Error>> {
    Err(Box::new(Decline(msg.into())))
}

macro_rules! reject {
    ($($arg:tt)+) => {
        ::std::panic::panic_any($crate::outcome::Rejection(::std::format!($($arg)+)))
    };
}
pub(crate) use reject;

macro_rules! unsupported {
    ($($arg:tt)+) => {
        ::std::panic::panic_any($crate::outcome::Decline(::std::format!($($arg)+)))
    };
}
pub(crate) use unsupported;

macro_rules! ensure {
    ($cond:expr $(,)?) => {
        if !$cond {
            $crate::outcome::reject!("check failed: {}", ::std::stringify!($cond))
        }
    };
    ($cond:expr, $($arg:tt)+) => {
        if !$cond {
            $crate::outcome::reject!($($arg)+)
        }
    };
}
pub(crate) use ensure;

macro_rules! ensure_eq {
    ($left:expr, $right:expr $(,)?) => {
        match (&$left, &$right) {
            (left, right) => {
                if !(*left == *right) {
                    $crate::outcome::reject!(
                        "check failed: {} == {} (left: {:?}, right: {:?})",
                        ::std::stringify!($left),
                        ::std::stringify!($right),
                        left,
                        right
                    )
                }
            }
        }
    };
    ($left:expr, $right:expr, $($arg:tt)+) => {
        match (&$left, &$right) {
            (left, right) => {
                if !(*left == *right) {
                    $crate::outcome::reject!(
                        "{} (left: {:?}, right: {:?})",
                        ::std::format_args!($($arg)+),
                        left,
                        right
                    )
                }
            }
        }
    };
}
pub(crate) use ensure_eq;
