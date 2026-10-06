// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::context::ExportFile;
use crate::frontend::parser::{parse_export_file, parse_export_mapped};
use crate::outcome::CheckError;
use bumpalo::Bump;
use std::error::Error;
use std::fs::OpenOptions;
use std::path::{Path, PathBuf};

const STANDARD_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisallowedAxiom {
    Warn,
    Reject,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AxiomDecision {
    Allow,
    Warn,
    Reject,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AxiomPolicy {
    Allow {
        names: Vec<String>,
        on_disallowed: DisallowedAxiom,
    },
    AllowAll,
}

impl Default for AxiomPolicy {
    fn default() -> Self {
        Self::Allow {
            names: STANDARD_AXIOMS
                .iter()
                .map(|name| (*name).to_owned())
                .collect(),
            on_disallowed: DisallowedAxiom::Warn,
        }
    }
}

impl AxiomPolicy {
    pub(crate) fn decision(&self, name: &str) -> AxiomDecision {
        match self {
            Self::AllowAll => AxiomDecision::Allow,
            Self::Allow { names, .. } if names.iter().any(|allowed| allowed == name) => {
                AxiomDecision::Allow
            }
            Self::Allow {
                on_disallowed: DisallowedAxiom::Warn,
                ..
            } => AxiomDecision::Warn,
            Self::Allow {
                on_disallowed: DisallowedAxiom::Reject,
                ..
            } => AxiomDecision::Reject,
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Output {
    pub verbose: bool,
    pub live: bool,
    pub color: bool,
}

#[derive(Debug, Clone)]
#[expect(clippy::struct_excessive_bools)]
pub struct Config {
    pub export_file_path: Option<PathBuf>,
    pub use_stdin: bool,
    pub axiom_policy: AxiomPolicy,
    pub num_threads: usize,
    pub parse_only: bool,
    pub nat_extension: bool,
    pub string_extension: bool,
    pub output: Output,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            export_file_path: None,
            use_stdin: false,
            axiom_policy: AxiomPolicy::default(),
            num_threads: 1,
            parse_only: false,
            nat_extension: false,
            string_extension: false,
            output: Output::default(),
        }
    }
}

impl Config {
    pub fn to_export_file(self, arena: &Bump) -> Result<ExportFile<'_>, Box<dyn Error>> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.parse(arena))) {
            Ok(result) => result,
            Err(payload) => match CheckError::from_panic(payload) {
                CheckError::Rejected(r) => Err(Box::new(r)),
                CheckError::Declined(d) => Err(Box::new(d)),
                CheckError::Internal(payload) => std::panic::resume_unwind(payload),
            },
        }
    }

    fn parse(self, arena: &Bump) -> Result<ExportFile<'_>, Box<dyn Error>> {
        let use_stdin = self.use_stdin || self.export_file_path.as_deref() == Some(Path::new("-"));
        if use_stdin {
            parse_export_file(arena, std::io::stdin(), self)
        } else if let Some(pathbuf) = self.export_file_path.as_ref() {
            match OpenOptions::new().read(true).truncate(false).open(pathbuf) {
                Ok(file) => {
                    let map =
                        unsafe { memmap2::Mmap::map(&file) }.map_err(|e| -> Box<dyn Error> {
                            Box::from(format!("Failed to map export file: {e:?}"))
                        })?;
                    parse_export_mapped(arena, &map, self)
                }
                Err(e) => Err(Box::from(format!("Failed to open export file: {e:?}"))),
            }
        } else {
            Err("must provide an export file path or enable stdin".into())
        }
    }
}
