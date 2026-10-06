// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use bumpalo::Bump;
use clap::{ArgGroup, Parser};
use sokonanoda::{AxiomPolicy, CheckError, Config, Decline, DisallowedAxiom, Output, Rejection};
use std::io::{IsTerminal, Write};
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::time::Instant;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const EXIT_ACCEPT: i32 = 0;
const EXIT_REJECT: i32 = 1;
const EXIT_DECLINE: i32 = 2;
const EXIT_INTERNAL: i32 = 3;

const EXIT_CODES: &str = "Exit status:
  0  accepted
  1  rejected
  2  declined: the export uses something this checker does not support
  3  internal error";

const DEFAULT_THREADS: usize = 4;

#[derive(Debug, Parser)]
#[expect(clippy::struct_excessive_bools)]
#[command(
    version,
    about = "Check a Lean export",
    after_help = EXIT_CODES,
    group(ArgGroup::new("input").required(true).multiple(false))
)]
struct Cli {
    #[arg(
        value_name = "EXPORT",
        group = "input",
        help = "Export file to check, or - for standard input"
    )]
    export_file_path: Option<PathBuf>,

    #[arg(
        long = "stdin",
        group = "input",
        help_heading = "Input",
        help = "Read the export from standard input"
    )]
    use_stdin: bool,

    #[arg(
        long = "axiom-allow",
        value_name = "NAME[,NAME...]",
        value_delimiter = ',',
        conflicts_with = "axiom_allow_all",
        help_heading = "Axioms",
        help = "Allow only these axiom names; repeat the option or separate names with commas (replaces the default list)"
    )]
    axiom_allow: Vec<String>,

    #[arg(long = "axiom-allow-all", conflicts_with_all = ["axiom_allow", "axiom_ondisallowed_warn", "axiom_ondisallowed_reject"], help_heading = "Axioms", help = "Allow every axiom")]
    axiom_allow_all: bool,

    #[arg(long = "axiom-ondisallowed-warn", conflicts_with_all = ["axiom_allow_all", "axiom_ondisallowed_reject"], help_heading = "Axioms", help = "Report disallowed axioms (default)")]
    axiom_ondisallowed_warn: bool,

    #[arg(long = "axiom-ondisallowed-reject", conflicts_with_all = ["axiom_allow_all", "axiom_ondisallowed_warn"], help_heading = "Axioms", help = "Reject an export containing a disallowed axiom")]
    axiom_ondisallowed_reject: bool,

    #[arg(
        short = 'j',
        long = "threads",
        value_name = "N",
        help_heading = "Checking",
        help = "Number of checker threads [default: available cores, at most 4]"
    )]
    num_threads: Option<NonZeroUsize>,

    #[arg(long, help_heading = "Checking", help = "Enable native Nat reduction")]
    nat_extension: bool,

    #[arg(
        long,
        help_heading = "Checking",
        help = "Enable native String reduction"
    )]
    string_extension: bool,

    #[arg(
        long,
        help_heading = "Checking",
        help = "Parse the export without typechecking declarations"
    )]
    parse_only: bool,

    #[arg(
        short,
        long,
        conflicts_with = "quiet",
        help_heading = "Output",
        help = "Print one line per checked declaration"
    )]
    verbose: bool,

    #[arg(
        short,
        long,
        help_heading = "Output",
        help = "Print nothing on success"
    )]
    quiet: bool,
}

fn config(cli: Cli) -> (Config, bool) {
    let stdout_tty = std::io::stdout().is_terminal();
    let no_color = std::env::var_os("NO_COLOR").is_some_and(|v| !v.is_empty());
    let output = Output {
        verbose: cli.verbose,
        live: stdout_tty && !cli.verbose && !cli.quiet,
        color: stdout_tty && !no_color,
    };
    let num_threads = cli.num_threads.map_or_else(
        || {
            std::thread::available_parallelism()
                .map_or(1, NonZeroUsize::get)
                .min(DEFAULT_THREADS)
        },
        NonZeroUsize::get,
    );
    let cfg = Config {
        export_file_path: cli.export_file_path,
        use_stdin: cli.use_stdin,
        axiom_policy: if cli.axiom_allow_all {
            AxiomPolicy::AllowAll
        } else {
            let names = if cli.axiom_allow.is_empty() {
                match AxiomPolicy::default() {
                    AxiomPolicy::Allow { names, .. } => names,
                    AxiomPolicy::AllowAll => unreachable!(),
                }
            } else {
                cli.axiom_allow
            };
            AxiomPolicy::Allow {
                names,
                on_disallowed: if cli.axiom_ondisallowed_reject {
                    DisallowedAxiom::Reject
                } else {
                    DisallowedAxiom::Warn
                },
            }
        },
        num_threads,
        parse_only: cli.parse_only,
        nat_extension: cli.nat_extension,
        string_extension: cli.string_extension,
        output,
    };
    (cfg, cli.quiet)
}

fn run(cfg: Config, quiet: bool) -> i32 {
    let start = Instant::now();
    let parse_only = cfg.parse_only;
    let arena = Bump::new();
    let export_file = match cfg.to_export_file(&arena) {
        Ok(parsed) => parsed,
        Err(e) => {
            eprintln!("{e}\n\n{HELP_SHORT}");
            return if e.is::<Decline>() {
                EXIT_DECLINE
            } else {
                EXIT_REJECT
            };
        }
    };
    let n = export_file.num_declars();
    let done = if parse_only { "parsed" } else { "checked" };
    match export_file.check_all_declars() {
        Ok(()) => {
            if !quiet {
                let _ = writeln!(
                    std::io::stdout(),
                    "{done} {n} declarations in {:.3}s",
                    start.elapsed().as_secs_f64()
                );
            }
            EXIT_ACCEPT
        }
        Err(e @ CheckError::Rejected(_)) => {
            eprintln!("{e}");
            EXIT_REJECT
        }
        Err(e @ CheckError::Declined(_)) => {
            eprintln!("{e}");
            EXIT_DECLINE
        }
        Err(CheckError::Internal(_)) => EXIT_INTERNAL,
    }
}

fn main() {
    let (cfg, quiet) = config(Cli::parse());
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let payload = info.payload();
        if !payload.is::<Rejection>() && !payload.is::<Decline>() {
            eprint!("internal error: ");
            default_hook(info);
        }
    }));
    let code = std::panic::catch_unwind(|| run(cfg, quiet)).unwrap_or(EXIT_INTERNAL);
    std::process::exit(code);
}

const HELP_SHORT: &str = "run with `--help` for command-line options";
