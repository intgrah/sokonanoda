//! Placeholder:
//! ```ignore
//! Doc comment example
//! ```
pub mod checker;
pub mod config;
pub mod frontend;
pub mod term;

pub use checker::{
    conv, debug_printer, env, eval, inductive, infer, quot, quote, relevance, tc, value,
};
pub use frontend::parser;
pub use term::{expr, level, name};

pub(crate) const STACK_SIZE: usize = 2 * 1024 * 1024 * 1024;
