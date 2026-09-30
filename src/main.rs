use bumpalo::Bump;
use clap::{ArgGroup, Parser};
use sokonanoda::config::{AxiomPolicy, Config, DisallowedAxiom};
use std::error::Error;
use std::num::NonZeroUsize;
use std::path::PathBuf;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const EXIT_REJECT: i32 = 1;
const EXIT_DECLINE: i32 = 2;

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

fn main() {
    let cfg = Config::from(Cli::parse());
    let result = std::panic::catch_unwind(|| -> Result<(), Box<dyn Error>> {
        let arena = Bump::new();
        let (export_file, warned_axioms) = cfg.to_export_file(&arena)?;
        if !warned_axioms.is_empty() {
            eprintln!("warning: disallowed axioms: {}", warned_axioms.join(", "));
        }
        if export_file.config.parse_only {
            println!("Parsed {} declarations", export_file.declars.len());
            return Ok(());
        }

        export_file.check_all_declars();
        if export_file.config.print_success_message {
            println!(
                "Checked {} declarations with no errors",
                export_file.declars.len()
            );
        }
        Ok(())
    });

    match result {
        Ok(Ok(())) => {}
        Ok(Err(e)) => {
            let declined = e
                .downcast_ref::<sokonanoda::frontend::error::Decline>()
                .is_some();
            eprintln!("{e}\n\n{HELP_SHORT}");
            std::process::exit(if declined { EXIT_DECLINE } else { EXIT_REJECT });
        }
        Err(_) => std::process::exit(EXIT_REJECT),
    }
}

const HELP_SHORT: &str = "run with `--help` for command-line options";
