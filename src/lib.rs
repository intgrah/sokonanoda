//! Placeholder:
//! ```ignore
//! Doc comment example
//! ```
#![allow(clippy::too_many_arguments)]
#![deny(clippy::cast_possible_truncation)]

pub mod config;
pub mod conv;
pub mod debug_printer;
pub mod env;
pub mod eval;
pub mod expr;
pub mod inductive;
pub mod infer;
pub mod level;
pub mod name;
mod nat;
pub mod parser;
pub mod quot;
pub mod quote;
pub mod relevance;
pub mod tc;
pub mod util;
pub mod value;

pub(crate) const STACK_SIZE: usize = 2 * 1024 * 1024 * 1024;
