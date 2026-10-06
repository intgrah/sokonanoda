// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::env::Declar;
use crate::config::{AxiomDecision, AxiomPolicy, Config, Output};
use crate::outcome::{Decline, Rejection};
use std::any::Any;
use std::io::{BufWriter, Stdout, Write};
use std::panic::AssertUnwindSafe;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
use std::sync::{Mutex, PoisonError};
use std::time::{Duration, Instant};

const LIVE_INTERVAL: Duration = Duration::from_millis(50);
const LABEL_WIDTH: usize = 8;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Status {
    Ok,
    Warn,
    Reject,
    Decline,
    Error,
}

impl Status {
    fn label(self) -> &'static str {
        match self {
            Status::Ok => "ok",
            Status::Warn => "warn",
            Status::Reject => "reject",
            Status::Decline => "decline",
            Status::Error => "error",
        }
    }

    fn color(self) -> &'static str {
        match self {
            Status::Ok => "32",
            Status::Warn | Status::Decline => "33",
            Status::Reject | Status::Error => "31",
        }
    }
}

fn terminal_width() -> Option<usize> {
    let mut ws = libc::winsize {
        ws_row: 0,
        ws_col: 0,
        ws_xpixel: 0,
        ws_ypixel: 0,
    };
    let r = unsafe { libc::ioctl(libc::STDOUT_FILENO, libc::TIOCGWINSZ, &raw mut ws) };
    (r == 0 && ws.ws_col > 0).then_some(usize::from(ws.ws_col))
}

struct Screen {
    out: Option<BufWriter<Stdout>>,
    live_shown: bool,
    live_at: Option<Instant>,
}

impl Screen {
    fn emit(&mut self, text: &str, flush: bool) {
        let Some(out) = &mut self.out else {
            return;
        };
        let written = out
            .write_all(text.as_bytes())
            .and_then(|()| if flush { out.flush() } else { Ok(()) });
        if written.is_err() {
            self.out = None;
        }
    }
}

pub(crate) struct Reporter {
    output: Output,
    axiom_policy: AxiomPolicy,
    live_width: Option<usize>,
    total: usize,
    width: usize,
    done: AtomicUsize,
    screen: Mutex<Screen>,
    stopped: AtomicBool,
}

impl Reporter {
    pub(crate) fn new(config: &Config, total: usize) -> Self {
        let output = config.output;
        Reporter {
            output,
            axiom_policy: config.axiom_policy.clone(),
            live_width: if output.live { terminal_width() } else { None },
            total,
            width: total.to_string().len(),
            done: AtomicUsize::new(0),
            screen: Mutex::new(Screen {
                out: Some(BufWriter::new(std::io::stdout())),
                live_shown: false,
                live_at: None,
            }),
            stopped: AtomicBool::new(false),
        }
    }

    pub(crate) fn stopped(&self) -> bool {
        self.stopped.load(Relaxed)
    }

    pub(crate) fn check(&self, d: &Declar<'_>, f: impl FnOnce()) {
        let start = Instant::now();
        let result = std::panic::catch_unwind(AssertUnwindSafe(f));
        let status = match &result {
            Ok(()) if self.warned(d) => Status::Warn,
            Ok(()) => Status::Ok,
            Err(p) if p.is::<Rejection>() => Status::Reject,
            Err(p) if p.is::<Decline>() => Status::Decline,
            Err(_) => Status::Error,
        };
        self.record(d, status, start.elapsed());
        if let Err(payload) = result {
            self.stopped.store(true, Relaxed);
            std::panic::resume_unwind(locate(d, payload));
        }
    }

    fn warned(&self, d: &Declar<'_>) -> bool {
        matches!(d, Declar::Axiom { .. })
            && self.axiom_policy.decision(&d.info().name.to_string()) == AxiomDecision::Warn
    }

    fn record(&self, d: &Declar<'_>, status: Status, elapsed: Duration) {
        let persist = self.output.verbose || status != Status::Ok;
        if !persist && self.live_width.is_none() {
            self.done.fetch_add(1, Relaxed);
            return;
        }
        let mut screen = self.screen.lock().unwrap_or_else(PoisonError::into_inner);
        let done = self.done.fetch_add(1, Relaxed) + 1;
        let now = Instant::now();
        if !persist && screen.live_at.is_some_and(|at| now - at < LIVE_INTERVAL) {
            return;
        }
        let (total, width) = (self.total, self.width);
        let prefix = format!("{done:>width$}/{total}  ");
        let rest = format!(
            "{:<9}  {:>9.3}ms  {}",
            d.kind(),
            elapsed.as_secs_f64() * 1e3,
            d.info().name
        );
        let label = status.label();
        let pad = " ".repeat(LABEL_WIDTH - label.len());
        let label = if self.output.color {
            format!("\x1b[{}m{label}\x1b[0m", status.color())
        } else {
            label.to_owned()
        };
        let clear = if screen.live_shown { "\r\x1b[2K" } else { "" };
        let text = if persist {
            screen.live_shown = false;
            format!("{clear}{prefix}{label}{pad}{rest}\n")
        } else {
            let room = self
                .live_width
                .map_or(0, |w| w.saturating_sub(prefix.len() + LABEL_WIDTH + 1));
            let rest: String = rest.chars().take(room).collect();
            screen.live_shown = true;
            screen.live_at = Some(now);
            format!("{clear}{prefix}{label}{pad}{rest}")
        };
        screen.emit(&text, !self.output.verbose || self.output.color);
    }

    pub(crate) fn finish(&self) {
        let mut screen = self.screen.lock().unwrap_or_else(PoisonError::into_inner);
        let clear = if screen.live_shown { "\r\x1b[2K" } else { "" };
        screen.live_shown = false;
        screen.emit(clear, true);
    }
}

fn locate(d: &Declar<'_>, payload: Box<dyn Any + Send>) -> Box<dyn Any + Send> {
    let at = format!("{} {}", d.kind(), d.info().name);
    match payload.downcast::<Rejection>() {
        Ok(r) => Box::new(Rejection(format!("{at}: {}", r.0))),
        Err(payload) => match payload.downcast::<Decline>() {
            Ok(r) => Box::new(Decline(format!("{at}: {}", r.0))),
            Err(payload) => payload,
        },
    }
}
