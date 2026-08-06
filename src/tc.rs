use crate::env::{Declar, DeclarInfo, Env, EnvLimit};
use crate::util::{
    ExportFile, ExprPtr, TcCache, TcCtx
};
use crate::value::E;

use InferFlag::*;

const SESSION_BUDGET: usize = 1 << 20;

const CHUNK_SIZE: usize = 64;

/// An enum for type safety and convenience; used during nat literal reduction, and also for testing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NatBinOp {
    Add,
    Sub,
    Mul,
    Pow,
    Mod,
    Div,
    Beq,
    Ble,
    Gcd,
    LAnd,
    LOr,
    XOr,
    Shl,
    Shr,
}

/// A flag that accompanies calls to type inference; if the flag is `Check`,
/// we perform additional definitional equality checks (for example, the type of an
/// argument to a lambda is the same type as the binder in the labmda). These checks
/// are costly however, and in some cases we're using inference during reduction of
/// expressions we know to be well-typed, so we can pass the flag `InferOnly` to omit
/// these checks when they are not needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum InferFlag {
    InferOnly,
    Check,
}

pub struct TypeChecker<'x, 't, 'p> {
    pub(crate) ctx: &'x mut TcCtx<'t, 'p>,
    /// An immutable reference to an environment, which contains declarations and notation.
    /// To accommodate the temporary declarations created while checking nested inductives,
    /// the environment may have a temporary extension which also holds declarations, and
    /// is searched before the persistent environment.
    ///
    /// This is stored as a field in `TypeChecker` rather than being placed in `TcCtx` so
    /// that the borrow checker will allow us to mutably reference `TcCtx` while we have
    /// outstanding references to environment declarations. Rust can tell that borrows
    /// of different struct fields are exclusive, but it can't analyze what fields of a given
    /// field's type are being exclusively borrowed.
    pub(crate) env: &'x Env<'x, 't>,
    /// The caches for things like inference, reduction, and equality checking.
    pub(crate) tc_cache: &'x mut TcCache<'t, 't>,
    pub(crate) arena: &'t bumpalo::Bump,
    /// If this type checker is being used to check a simple declaration, this field will
    /// contain the universe parameters of that declaration. This is used in a couple of places
    /// to make sure that all of the universe paramters actually used in a declaration `d` are
    /// properly represented in the declaration's uparams info.
    pub(crate) declar_info: Option<DeclarInfo<'t>>,
    pub(crate) nat_extension: bool,
}

impl<'p> ExportFile<'p> {
    /// The entry point for checking a declaration `d`.
    pub fn check_declar(&self, d: &Declar<'p>) {
        self.with_ctx(|ctx, cache, bump| self.check_declar_with(ctx, cache, bump, d))
    }

    fn check_declar_with<'t>(
        &'t self,
        ctx: &mut TcCtx<'t, 'p>,
        cache: &mut TcCache<'t, 't>,
        bump: &'t bumpalo::Bump,
        d: &Declar<'t>,
    ) {
        use Declar::*;
        match d {
            Inductive(..) => self.check_inductive_declar(ctx, cache, bump, d),
            Quot { .. } => crate::quot::check_quot(ctx, cache, bump, d),
            _ => self.check_simple_declar(ctx, cache, bump, d),
        }
    }

    fn check_simple_declar<'t>(
        &'t self,
        ctx: &mut TcCtx<'t, 'p>,
        cache: &mut TcCache<'t, 't>,
        bump: &'t bumpalo::Bump,
        d: &Declar<'t>,
    ) {
        use Declar::*;
        let env = self.new_env(EnvLimit::ByName(d.info().name));
        let mut tc = TypeChecker::new(ctx, &env, bump, Some(*d.info()), cache);
        match d {
            Definition { val, .. } | Theorem { val, .. } | Opaque { val, .. } => tc.check_def_like_v(d, *val),
            Axiom { .. } | Constructor(..) | Recursor(..) => tc.check_declar_info_v(d),
            Inductive(..) | Quot { .. } => unreachable!(),
        }
        match d {
            Constructor(ctor_data) => assert!(self.declars.get(&ctor_data.inductive_name).is_some()),
            Recursor(recursor_data) =>
                for ind_name in recursor_data.all_inductives.iter() {
                    assert!(self.declars.get(ind_name).is_some())
                },
            _ => {}
        }
    }

    fn run_session<F>(&self, first: (usize, usize), mut next_chunk: F)
    where
        F: FnMut() -> Option<(usize, usize)>, {
        let mut thread_arena = stumpalo::Arena::new();
        thread_arena.with_scope(|tscope| {
            let mut tctx = TcCtx::new(self, tscope);
            self.run_session_inner(first, &mut next_chunk, &mut tctx)
        })
    }

    fn run_session_inner<'h, F>(&'h self, first: (usize, usize), next_chunk: &mut F, tctx: &mut TcCtx<'h, 'p>)
    where
        F: FnMut() -> Option<(usize, usize)>, {
        let base = bumpalo::Bump::new();
        let mut session_cache = crate::util::SessionCache::new(&base);
        let mut sbump = crate::util::SessionBump::new();
        let mut pending = Some(first);
        loop {
            let finished = session_cache.enter(|cache| loop {
                let Some((mut i, end)) = pending.take().or_else(&mut *next_chunk) else { return true };
                while i < end {
                    let (_, d) = self.declars.get_index(i).expect("declaration index out of range");
                    i += 1;
                    self.check_declar_with(tctx, cache, sbump.get(), d);
                    if sbump.allocated_bytes() > SESSION_BUDGET {
                        pending = Some((i, end));
                        return false
                    }
                }
            });
            sbump.reset();
            tctx.expr_cache.shrink();
            if finished {
                return
            }
        }
    }

    /// Check all declarations in this export file using a single thread.
    pub(crate) fn check_all_declars_serial(&self) {
        let total = self.declars.len();
        std::thread::scope(|sco| {
            std::thread::Builder::new()
                .stack_size(crate::STACK_SIZE)
                .spawn_scoped(sco, || self.run_session((0, total), || None))
                .unwrap()
                .join()
                .expect("serial checker thread panicked");
        });
    }

    /// Check all declarations in this export file, spawning `num_threads` as
    fn check_all_declars_par(&self, num_threads: usize) {
        use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
        use std::thread;
        let task_num = AtomicUsize::new(0);
        let total = self.declars.len();
        let claim = || {
            let start = task_num.fetch_add(CHUNK_SIZE, Relaxed);
            if start >= total {
                None
            } else {
                Some((start, (start + CHUNK_SIZE).min(total)))
            }
        };
        thread::scope(|sco| {
            let mut handles = Vec::new();
            for i in 0..num_threads {
                handles.push(
                    thread::Builder::new()
                        .name(format!("thread_{}", i))
                        .stack_size(crate::STACK_SIZE)
                        .spawn_scoped(sco, || {
                            if let Some(first) = claim() {
                                self.run_session(first, claim);
                            }
                        })
                        .unwrap(),
                )
            }
            for t in handles {
                t.join().expect("A thread in `check_all_declars` panicked while being joined");
            }
        });
    }

    /// Check all of the declarations in this export file on the specified number
    /// of threads (checking will be serial on the main thread is num_threads <= 1).
    pub fn check_all_declars(&self) {
        if self.config.num_threads > 1 {
            self.check_all_declars_par(self.config.num_threads)
        } else {
            self.check_all_declars_serial()
        }
    }
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub fn new(
        dag: &'x mut TcCtx<'t, 'p>,
        env: &'x Env<'x, 't>,
        arena: &'t bumpalo::Bump,
        declar_info: Option<DeclarInfo<'t>>,
        tc_cache: &'x mut TcCache<'t, 't>,
    ) -> Self {
        let nat_extension = dag.export_file.config.nat_extension;
        Self { ctx: dag, env, tc_cache, arena, declar_info, nat_extension }
    }

    #[inline]
    pub(crate) fn empty_env(&self) -> E<'t> { self.tc_cache.empty_env }

    #[inline]
    pub(crate) fn empty_spine(&self) -> crate::value::S<'t> { self.tc_cache.empty_spine }

    #[inline]
    pub(crate) fn empty_ctx(&self) -> crate::value::C<'t> { self.tc_cache.empty_ctx }

    pub fn assert_def_eq(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>) {
        assert!(self.def_eq_core(u, v), "def_eq failed");
    }








    pub fn is_proposition(&mut self, e: ExprPtr<'t>) -> bool {
        let depth = 0u32;
        let env = self.empty_env();
        let v = self.eval(depth, env, e);
        self.is_prop_type(depth, v)
    }

    pub fn is_proof(&mut self, e: ExprPtr<'t>) -> bool {
        let depth = 0u32;
        let env = self.empty_env();
        let ctx = self.empty_ctx();
        let ty = self.infer_value(InferOnly, depth, env, ctx, e);
        self.is_prop_type(depth, ty)
    }
}
