// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use bumpalo::Bump;
use clap::{ArgGroup, Parser};
use sokonanoda::{AxiomPolicy, CheckError, Config, Decline, DisallowedAxiom, Rejection};
use std::num::NonZeroUsize;
use std::path::PathBuf;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const EXIT_ACCEPT: i32 = 0;
const EXIT_REJECT: i32 = 1;
const EXIT_DECLINE: i32 = 2;
const EXIT_INTERNAL: i32 = 3;

#[derive(Debug, Parser)]
#[expect(clippy::struct_excessive_bools)]
#[command(version, about = "Check a Lean export", group(ArgGroup::new("input").required(true).multiple(false)))]
struct Cli {
    #[arg(value_name = "EXPORT", group = "input", help = "Export file to check")]
    export_file_path: Option<PathBuf>,

    #[arg(
        long = "stdin",
        group = "input",
        help = "Read the export from standard input"
    )]
    use_stdin: bool,

    #[arg(
        long = "axiom-allow",
        value_name = "NAME[,NAME...]",
        value_delimiter = ',',
        conflicts_with = "axiom_allow_all",
        help = "Allow only these axiom names; repeat the option or separate names with commas (replaces the default list)"
    )]
    axiom_allow: Vec<String>,

    #[arg(long = "axiom-allow-all", conflicts_with_all = ["axiom_allow", "axiom_ondisallowed_warn", "axiom_ondisallowed_reject"], help = "Allow every axiom")]
    axiom_allow_all: bool,

    #[arg(long = "axiom-ondisallowed-warn", conflicts_with_all = ["axiom_allow_all", "axiom_ondisallowed_reject"], help = "Report disallowed axioms (default)")]
    axiom_ondisallowed_warn: bool,

    #[arg(long = "axiom-ondisallowed-reject", conflicts_with_all = ["axiom_allow_all", "axiom_ondisallowed_warn"], help = "Reject an export containing a disallowed axiom")]
    axiom_ondisallowed_reject: bool,

    #[arg(short = 'j', long = "threads", default_value_t = NonZeroUsize::new(1).unwrap(), help = "Number of checker threads")]
    num_threads: NonZeroUsize,

    #[arg(long, help = "Parse the export without typechecking declarations")]
    parse_only: bool,

    #[arg(long, help = "Enable native Nat reduction")]
    nat_extension: bool,

    #[arg(long, help = "Enable native String reduction")]
    string_extension: bool,

    #[arg(long, help = "Print a summary after a successful check")]
    print_success_message: bool,
}

impl From<Cli> for Config {
    fn from(cli: Cli) -> Self {
        Config {
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
            num_threads: cli.num_threads.get(),
            parse_only: cli.parse_only,
            nat_extension: cli.nat_extension,
            string_extension: cli.string_extension,
            print_success_message: cli.print_success_message,
        }
    }
}

fn run(cfg: Config) -> i32 {
    let parse_only = cfg.parse_only;
    let print_success_message = cfg.print_success_message;
    let arena = Bump::new();
    let (export_file, warned_axioms) = match cfg.to_export_file(&arena) {
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
    if !warned_axioms.is_empty() {
        eprintln!("warning: disallowed axioms: {}", warned_axioms.join(", "));
    }
    if parse_only {
        println!("Parsed {} declarations", export_file.num_declars());
        return EXIT_ACCEPT;
    }
    match export_file.check_all_declars() {
        Ok(()) => {
            if print_success_message {
                println!(
                    "Checked {} declarations with no errors",
                    export_file.num_declars()
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
    let cfg = Config::from(Cli::parse());
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let payload = info.payload();
        if !payload.is::<Rejection>() && !payload.is::<Decline>() {
            eprint!("internal error: ");
            default_hook(info);
        }
    }));
    let code = std::panic::catch_unwind(|| run(cfg)).unwrap_or(EXIT_INTERNAL);
    std::process::exit(code);
}

const HELP_SHORT: &str = "run with `--help` for command-line options";
