//! Proof-of-concept for the arena + tagged-pointer + hash-cons redesign.
//!
//! Validates the load-bearing, highest-risk mechanics BEFORE touching the real
//! codebase:
//!   1. strict-provenance low-bit tagged pointer newtype (NonNull + map_addr/addr)
//!   2. covariance: `ExprPtr<'g>` coerces to `ExprPtr<'scope>` when `'g: 'scope`
//!   3. hash-cons interner over `hashbrown::HashTable<&'a Expr<'a>>`
//!   4. global `Arena` (frozen, shared `&'g`, Sync) + per-thread local `Arena`
//!   5. `with_scope` per-task reuse loop; mixed-arena children ("meet to local")
//!   6. `std::thread::scope` workers sharing `&'g` frozen global, own local arena
//!
//! Run with: `cargo run --example arena_poc`

use hashbrown::HashTable;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::Deref;
use std::ptr::NonNull;
use stumpalo::{Arena, ArenaRef};

// ---- the node type (mini version of `Expr`) ----

#[derive(Clone, Copy)]
enum Expr<'a> {
    Var { hash: u64, idx: u32 },
    App { hash: u64, fun: ExprPtr<'a>, arg: ExprPtr<'a> },
}

impl<'a> Expr<'a> {
    fn get_hash(&self) -> u64 {
        match self {
            Expr::Var { hash, .. } | Expr::App { hash, .. } => *hash,
        }
    }
}

const _: () = assert!(std::mem::align_of::<Expr<'static>>() >= 2);

// ---- tagged pointer (tag bit 0 = global, 1 = local) ----

struct ExprPtr<'a> {
    ptr: NonNull<Expr<'a>>,
    _ph: PhantomData<&'a Expr<'a>>,
}

impl<'a> Clone for ExprPtr<'a> {
    fn clone(&self) -> Self { *self }
}
impl<'a> Copy for ExprPtr<'a> {}

// Logically a shared `&'a Expr`; NonNull blocks the auto-impls, so re-assert.
unsafe impl<'a> Send for ExprPtr<'a> {}
unsafe impl<'a> Sync for ExprPtr<'a> {}

impl<'a> ExprPtr<'a> {
    #[inline]
    fn global(r: &'a Expr<'a>) -> Self { ExprPtr { ptr: NonNull::from(r), _ph: PhantomData } }
    #[inline]
    fn local(r: &'a Expr<'a>) -> Self {
        let tagged = NonNull::from(r).as_ptr().map_addr(|a| a | 1);
        ExprPtr { ptr: unsafe { NonNull::new_unchecked(tagged) }, _ph: PhantomData }
    }
    #[inline]
    fn is_local(self) -> bool { self.ptr.as_ptr().addr() & 1 == 1 }
    #[inline]
    fn as_ref(self) -> &'a Expr<'a> { unsafe { &*self.ptr.as_ptr().map_addr(|a| a & !1) } }
}

impl<'a> Deref for ExprPtr<'a> {
    type Target = Expr<'a>;
    #[inline]
    fn deref(&self) -> &Expr<'a> { self.as_ref() }
}

impl<'a> PartialEq for ExprPtr<'a> {
    #[inline]
    fn eq(&self, o: &Self) -> bool { self.ptr.as_ptr().addr() == o.ptr.as_ptr().addr() }
}
impl<'a> Eq for ExprPtr<'a> {}
impl<'a> Hash for ExprPtr<'a> {
    #[inline]
    fn hash<H: Hasher>(&self, s: &mut H) { s.write_u64(self.ptr.as_ptr().addr() as u64); }
}

// Lifetime-erased shallow structural equality (children compared by masked addr),
// so a `'g`-stored node can be compared against an `'scope` probe.
fn addr_of(p: ExprPtr<'_>) -> usize { p.ptr.as_ptr().addr() & !1 }
fn shallow_eq(stored: &Expr<'_>, probe: &Expr<'_>) -> bool {
    match (stored, probe) {
        (Expr::Var { idx: a, .. }, Expr::Var { idx: b, .. }) => a == b,
        (Expr::App { fun: f1, arg: a1, .. }, Expr::App { fun: f2, arg: a2, .. }) =>
            addr_of(*f1) == addr_of(*f2) && addr_of(*a1) == addr_of(*a2),
        _ => false,
    }
}

// ---- interner ----

struct Interner<'a> {
    table: HashTable<&'a Expr<'a>>,
}

impl<'a> Interner<'a> {
    fn new() -> Self { Interner { table: HashTable::new() } }
    fn get(&self, e: &Expr<'_>) -> Option<&'a Expr<'a>> { self.table.find(e.get_hash(), |p| shallow_eq(p, e)).copied() }
    fn intern(&mut self, arena: &ArenaRef<'a>, e: Expr<'a>) -> &'a Expr<'a> {
        if let Some(r) = self.get(&e) {
            return r;
        }
        let r: &'a Expr<'a> = arena.alloc(e);
        self.table.insert_unique(e.get_hash(), r, |p| p.get_hash());
        r
    }
}

// ---- frozen global view shared across threads ----

struct Frozen<'g> {
    exprs: Interner<'g>,
    roots: Vec<ExprPtr<'g>>,
}

// Must be Sync to share `&'g Frozen` across worker threads.
fn _assert_sync<T: Sync>() {}
fn _checks() {
    _assert_sync::<Frozen<'static>>();
    _assert_sync::<ExprPtr<'static>>();
}

fn mk_var_hash(idx: u32) -> u64 { idx as u64 ^ 0x9e3779b97f4a7c15 }
fn mk_app_hash(f: ExprPtr<'_>, a: ExprPtr<'_>) -> u64 {
    (addr_of(f) as u64).wrapping_mul(31).wrapping_add(addr_of(a) as u64)
}

// ---- local per-task context ----

struct TcCtx<'scope, 'g: 'scope> {
    global: &'scope Frozen<'g>,
    local: Interner<'scope>,
    arena: &'scope ArenaRef<'scope>,
}

impl<'scope, 'g: 'scope> TcCtx<'scope, 'g> {
    fn new(global: &'scope Frozen<'g>, arena: &'scope ArenaRef<'scope>) -> Self {
        TcCtx { global, local: Interner::new(), arena }
    }

    // local-first, then global unless local-tagged; returns a local-or-global ptr.
    fn alloc_expr(&mut self, e: Expr<'scope>) -> ExprPtr<'scope> {
        if let Some(r) = self.local.get(&e) {
            return ExprPtr::local(r);
        }
        let local_only = match e {
            Expr::Var { .. } => false,
            Expr::App { fun, arg, .. } => fun.is_local() || arg.is_local(),
        };
        if !local_only {
            // NOTE the coercion: `self.global.exprs.get` yields `&'g Expr<'g>`,
            // returned here as `ExprPtr<'scope>` — `'g: 'scope` covariance.
            if let Some(r) = self.global.exprs.get(&e) {
                return ExprPtr::global(r);
            }
        }
        ExprPtr::local(self.local.intern(self.arena, e))
    }

    fn mk_app(&mut self, fun: ExprPtr<'scope>, arg: ExprPtr<'scope>) -> ExprPtr<'scope> {
        let hash = mk_app_hash(fun, arg);
        self.alloc_expr(Expr::App { hash, fun, arg })
    }
}

fn build_global<'g>(gref: &'g ArenaRef<'g>) -> Frozen<'g> {
    let mut exprs = Interner::new();
    let mut roots = Vec::new();
    // intern vars 0..4 and an application (var0 var1), all tagged global
    let mut vars = Vec::new();
    for i in 0..4u32 {
        let r = exprs.intern(gref, Expr::Var { hash: mk_var_hash(i), idx: i });
        vars.push(ExprPtr::global(r));
    }
    let app_hash = mk_app_hash(vars[0], vars[1]);
    let app = exprs.intern(gref, Expr::App { hash: app_hash, fun: vars[0], arg: vars[1] });
    roots.push(ExprPtr::global(app));
    for v in vars {
        roots.push(v);
    }
    Frozen { exprs, roots }
}

fn check_one(global: &Frozen<'_>, scope: &ArenaRef<'_>, task: u32) -> (bool, bool, bool) {
    let mut ctx = TcCtx::new(global, scope);
    let g_app = global.roots[0]; // global (var0 var1)
    let g_var0 = global.roots[1];

    // (a) re-deriving the global app from global children dedups to the SAME global ptr.
    let rebuilt = ctx.mk_app(g_var0, global.roots[2]);
    let dedup_hit = rebuilt == g_app && !rebuilt.is_local();

    // (b) a novel local var, then a local app mixing a GLOBAL child and a LOCAL child.
    let local_var = ctx.alloc_expr(Expr::Var { hash: mk_var_hash(1000 + task), idx: 1000 + task });
    let mixed = ctx.mk_app(g_var0, local_var); // global fun + local arg
    let mixed_is_local = mixed.is_local();

    // (c) deref works regardless of arena; structural check via Deref.
    let deref_ok = matches!(*mixed, Expr::App { .. }) && matches!(*g_app, Expr::App { .. });

    (dedup_hit, mixed_is_local, deref_ok)
}

fn main() {
    let global_arena = Arena::new();
    let gref: &ArenaRef<'_> = global_arena.as_arena_ref();
    let frozen = build_global(gref);

    // Single-thread: per-task `with_scope` reuse loop.
    let mut local = Arena::new();
    for task in 0..3u32 {
        let out = local.with_scope(|scope| check_one(&frozen, scope, task));
        println!("task {task}: dedup_hit={} mixed_local={} deref_ok={}", out.0, out.1, out.2);
        assert_eq!(out, (true, true, true));
    }

    // Multi-thread: workers share `&frozen`, each owns a local arena + scope loop.
    let num_threads = 4u32;
    let counter = std::sync::atomic::AtomicU32::new(0);
    std::thread::scope(|s| {
        for _ in 0..num_threads {
            s.spawn(|| {
                let mut local = Arena::new();
                loop {
                    let task = counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if task >= 100 {
                        break;
                    }
                    let out = local.with_scope(|scope| check_one(&frozen, scope, task));
                    assert_eq!(out, (true, true, true));
                }
            });
        }
    });
    println!("multi-thread OK ({} tasks across {} threads)", 100, num_threads);
    println!("PoC passed.");
}
