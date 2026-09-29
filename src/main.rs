use sokonanoda::util::Config;
use std::error::Error;
use std::path::Path;
use stumpalo::Arena;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const EXIT_REJECT: i32 = 1;

const EXIT_DECLINE: i32 = 2;

fn main() {
    let mut args = std::env::args();
    let _ = args.next();
    let out = match args.next().as_ref() {
        None => Err(Box::from(
            "This program expects a path to a configuration file.".to_string(),
        )),
        Some(p) if p == "-h" || p == "--help" => {
            println!("{}", HELP_LONG);
            return;
        }
        Some(p) => {
            let path = Path::new(p).to_path_buf();
            match std::panic::catch_unwind(|| use_config(&path)) {
                Ok(r) => r,
                Err(_) => std::process::exit(EXIT_REJECT),
            }
        }
    };
    match out {
        Ok(Some(msg)) => println!("{}", msg),
        Ok(None) => {}
        Err(e) => {
            let declined = e.downcast_ref::<sokonanoda::util::Decline>().is_some();
            eprintln!("{:?}", MainError(e));
            std::process::exit(if declined { EXIT_DECLINE } else { EXIT_REJECT })
        }
    }
}

// Returns an optional success message.
fn use_config(config_path: &Path) -> Result<Option<String>, Box<dyn Error>> {
    let cfg = Config::try_from(config_path)?;
    let global_arena = Arena::new();
    let (export_file, skipped_axioms) = cfg.to_export_file(global_arena.as_arena_ref())?;
    if export_file.config.parse_only {
        return Ok(Some(format!(
            "Parsed {} declarations",
            export_file.declars.len()
        )));
    }
    // Check the environment
    export_file.check_all_declars();
    if export_file.config.print_success_message {
        if skipped_axioms.is_empty() {
            Ok(Some(format!(
                "Checked {} declarations with no errors",
                export_file.declars.len()
            )))
        } else {
            Ok(Some(format!(
                "Checked {} declarations with no errors, skipping exported but unpermitted axioms {:?}",
                export_file.declars.len(),
                skipped_axioms
            )))
        }
    } else if skipped_axioms.is_empty() {
        Ok(None)
    } else {
        Ok(Some(format!(
            "Skipped exported but unpermitted axioms {:?}",
            skipped_axioms
        )))
    }
}

struct MainError(Box<dyn Error>);

impl std::fmt::Debug for MainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}\n\n{}", self.0, HELP_SHORT)
    }
}

const HELP_SHORT: &str = "run with `-h` or `--help` for help";
const HELP_LONG: &str = concat!(
    "sokonanoda",
    " ",
    env!("CARGO_PKG_VERSION"),
    "\n\n",
    env!("CARGO_PKG_DESCRIPTION"),
    "\n\n",
    "get more help at ",
    env!("CARGO_PKG_REPOSITORY"),
    "\n\n",
    include_str!("../README.md")
);
