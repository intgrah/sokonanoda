use sokonanoda::pretty_printer::PpOptions;
use sokonanoda::util::Config;
use std::fs;
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};

const MAX_EXPORT_BYTES: u64 = 64 * 1024 * 1024;

fn arena_root() -> Option<PathBuf> { std::env::var_os("LEAN_KERNEL_ARENA").map(PathBuf::from) }

fn expected_outcome(root: &Path, stem: &str) -> Option<bool> {
    let spec = fs::read_to_string(root.join("tests").join(format!("{stem}.yaml"))).ok()?;
    spec.lines().find_map(|l| l.strip_prefix("outcome:")).map(|v| match v.trim() {
        "accept" => true,
        "reject" => false,
        other => panic!("bad outcome {other:?} for {stem}"),
    })
}

fn collect_cases(root: &Path, out: &mut Vec<(PathBuf, bool)>) {
    let Ok(entries) = fs::read_dir(root.join("_build/tests")) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().map(|e| e != "ndjson").unwrap_or(true) {
            continue;
        }
        if fs::metadata(&path).map(|m| m.len() > MAX_EXPORT_BYTES).unwrap_or(true) {
            continue;
        }
        let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
        if let Some(expect_accept) = expected_outcome(root, &stem) {
            out.push((path, expect_accept));
        }
    }
}

enum Outcome {
    Accepted,
    ParseError(String),
    KernelRejected(String),
    UnexpectedPanic(String),
}

fn run_case(export: PathBuf) -> Outcome {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || run_case_inner(export))
        .expect("spawn case thread")
        .join()
        .unwrap_or_else(|_| Outcome::UnexpectedPanic("thread join failed".to_string()))
}

fn run_case_inner(export: PathBuf) -> Outcome {
    let cfg = Config {
        export_file_path: Some(export),
        use_stdin: false,
        permitted_axioms: None,
        unpermitted_axiom_hard_error: false,
        num_threads: 1,
        nat_extension: true,
        string_extension: true,
        pp_declars: None,
        unknown_pp_declar_hard_error: false,
        pp_options: PpOptions::default(),
        pp_output_path: None,
        pp_to_stdout: false,
        print_success_message: false,
        print_axioms: false,
        unsafe_permit_all_axioms: true,
    };
    let ef = match cfg.to_export_file() {
        Ok((ef, _)) => ef,
        Err(e) => return Outcome::ParseError(format!("{e}")),
    };
    let result = panic::catch_unwind(AssertUnwindSafe(|| ef.check_all_declars()));
    match result {
        Ok(()) => Outcome::Accepted,
        Err(payload) => {
            let msg = if let Some(s) = payload.downcast_ref::<&str>() {
                (*s).to_string()
            } else if let Some(s) = payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "panic".to_string()
            };
            if msg == "def_eq failed" || msg.starts_with("def_eq") {
                Outcome::KernelRejected(msg)
            } else {
                Outcome::UnexpectedPanic(msg)
            }
        }
    }
}

#[test]
fn arena_fast_tier() {
    let Some(root) = arena_root() else {
        eprintln!("arena_fast_tier: LEAN_KERNEL_ARENA is not set; skipping");
        return;
    };
    let mut cases = Vec::new();
    collect_cases(&root, &mut cases);
    cases.sort();
    assert!(!cases.is_empty(), "no arena cases found under {}", root.display());

    if std::env::var("LEAN_KERNEL_ARENA_VERBOSE").is_err() {
        panic::set_hook(Box::new(|_| {}));
    }

    let mut failures = Vec::new();
    for (export, expect_accept) in &cases {
        let outcome = run_case(export.clone());
        let (got_accept, detail) = match &outcome {
            Outcome::Accepted => (true, "(accepted)".to_string()),
            Outcome::ParseError(e) => (false, format!("parse: {e}")),
            Outcome::KernelRejected(e) => (false, format!("kernel: {e}")),
            Outcome::UnexpectedPanic(e) => (false, format!("panic: {e}")),
        };
        let unexpected_panic = *expect_accept && matches!(outcome, Outcome::UnexpectedPanic(_));
        if got_accept != *expect_accept || unexpected_panic {
            let name = export.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
            failures.push(format!("{name}: expected accept={expect_accept}, got accept={got_accept} ({detail})"));
        }
    }

    if !failures.is_empty() {
        panic!("{}/{} arena cases mismatched:\n{}", failures.len(), cases.len(), failures.join("\n"));
    }
}
