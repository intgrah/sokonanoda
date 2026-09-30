// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

pub(crate) mod checker;
pub(crate) mod config;
pub(crate) mod frontend;
pub(crate) mod outcome;
pub(crate) mod term;

pub use checker::context::ExportFile;
pub use config::{AxiomPolicy, Config, DisallowedAxiom};
pub use outcome::{CheckError, Decline, Rejection};

pub(crate) const STACK_SIZE: usize = 2 * 1024 * 1024 * 1024;
