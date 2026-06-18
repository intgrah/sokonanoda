use crate::env::{DeclarMap, Env, EnvLimit, NotationMap};
use crate::expr::{BinderStyle, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;
use crate::pretty_printer::{PpOptions, PrettyPrinter};
use crate::tc::TypeChecker;
use crate::union_find::UnionFind;
use crate::unique_hasher::UniqueHasher;
use crate::value::{E, S, V};
use hashbrown::HashTable;
use indexmap::IndexMap;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{identities::Zero, Pow};
use rustc_hash::FxHasher;
use serde::Deserialize;
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs::OpenOptions;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::io::BufReader;
use std::io::BufWriter;
use std::io::Write;
use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use std::ptr::NonNull;
use stumpalo::{Arena, ArenaRef};

pub(crate) const fn default_true() -> bool { true }

pub(crate) type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;
pub(crate) type FxHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub(crate) type FxHashSet<K> = HashSet<K, BuildHasherDefault<FxHasher>>;
pub(crate) type UniqueHashMap<K, V> = HashMap<K, V, BuildHasherDefault<UniqueHasher>>;

pub(crate) type CowStr<'a> = Cow<'a, str>;

// --------------------------------------------------------------------------
// Tagged interning pointers.
//
// Each kernel item (`Name`, `Level`, `Expr`, string, bignum, level-slice) is
// allocated once into a bump arena and referred to by a real `&'a T` reference,
// hash-consed for structural uniqueness. The pointer carries a 1-bit tag in its
// low bit (strict-provenance): 0 = global (export file / persistent) arena,
// 1 = local (per-typecheck) arena. This is the direct relocation of the former
// `TC_BIT` marker from a synthetic 32-bit index to a real pointer.
//
// Pointer equality / hashing are by *address*; because items are interned,
// address identity == structural identity. The arenas never move allocations,
// so addresses are stable. Items in the global arena outlive items in the local
// arena, so a global `&'g T` coerces down to the local lifetime via covariance.
// --------------------------------------------------------------------------

// The `top-byte-ignore` feature relies on AArch64 hardware; reject it elsewhere.
#[cfg(all(feature = "top-byte-ignore", not(target_arch = "aarch64")))]
compile_error!("the `top-byte-ignore` feature requires the aarch64 target architecture (Top-Byte-Ignore)");

/// The bit set in an interning pointer's address to mark it as belonging to the
/// local (per-typecheck) arena. With `top-byte-ignore` the tag lives in the top
/// byte, which AArch64 ignores on dereference (so `as_ref` needs no masking);
/// otherwise it lives in the low bit, which is masked off on every dereference.
#[cfg(feature = "top-byte-ignore")]
const PTR_TAG: usize = 1 << 56;
#[cfg(not(feature = "top-byte-ignore"))]
const PTR_TAG: usize = 1;

/// A trait providing the precomputed structural hash used for hash-cons bucketing.
pub(crate) trait StructHash {
    fn struct_hash(&self) -> u64;
}
impl<T: Hash + ?Sized> StructHash for T {
    #[inline]
    fn struct_hash(&self) -> u64 {
        let mut hasher = FxHasher::default();
        self.hash(&mut hasher);
        hasher.finish()
    }
}

macro_rules! tagged_ptr {
    ($(#[$m:meta])* $name:ident, $pointee:ty) => {
        $(#[$m])*
        pub struct $name<'a> {
            ptr: NonNull<$pointee>,
            _ph: PhantomData<&'a $pointee>,
        }

        impl<'a> Clone for $name<'a> {
            #[inline]
            fn clone(&self) -> Self { *self }
        }
        impl<'a> Copy for $name<'a> {}

        // A tagged interning pointer is logically a shared `&'a $pointee`; the
        // `NonNull` field merely suppresses the auto traits, so re-assert them.
        unsafe impl<'a> Send for $name<'a> {}
        unsafe impl<'a> Sync for $name<'a> {}

        impl<'a> $name<'a> {
            /// Wrap a reference into the global (persistent) arena (tag 0).
            #[inline]
            pub(crate) fn global(r: &'a $pointee) -> Self {
                Self { ptr: NonNull::from(r), _ph: PhantomData }
            }

            /// Wrap a reference into the local (per-typecheck) arena, setting the
            /// tag bit while preserving pointer provenance.
            #[inline]
            pub(crate) fn local(r: &'a $pointee) -> Self {
                let tagged = NonNull::from(r).as_ptr().map_addr(|a| a | PTR_TAG);
                Self { ptr: unsafe { NonNull::new_unchecked(tagged) }, _ph: PhantomData }
            }

            /// `true` if this pointer refers to the local (TcCtx) arena.
            #[inline]
            pub(crate) fn is_local(self) -> bool { self.ptr.as_ptr().addr() & PTR_TAG != 0 }

            /// Recover the underlying reference. Under `top-byte-ignore` the tag
            /// lives in the top byte, which AArch64 ignores on dereference, so no
            /// masking is needed; otherwise the low tag bit is masked off.
            #[cfg(feature = "top-byte-ignore")]
            #[inline]
            pub(crate) fn as_ref(self) -> &'a $pointee { unsafe { &*self.ptr.as_ptr() } }
            #[cfg(not(feature = "top-byte-ignore"))]
            #[inline]
            pub(crate) fn as_ref(self) -> &'a $pointee {
                unsafe { &*self.ptr.as_ptr().map_addr(|a| a & !PTR_TAG) }
            }

            /// The (tagged) address, used as a cheap identity hash for caches.
            #[inline]
            #[allow(dead_code)]
            pub(crate) fn get_hash(&self) -> u64 { self.ptr.as_ptr().addr() as u64 }
        }

        impl<'a> std::ops::Deref for $name<'a> {
            type Target = $pointee;
            #[inline]
            fn deref(&self) -> &$pointee { self.as_ref() }
        }

        impl<'a> PartialEq for $name<'a> {
            #[inline]
            fn eq(&self, o: &Self) -> bool { self.ptr.as_ptr().addr() == o.ptr.as_ptr().addr() }
        }
        impl<'a> Eq for $name<'a> {}

        impl<'a> std::hash::Hash for $name<'a> {
            #[inline]
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                state.write_u64(self.ptr.as_ptr().addr() as u64)
            }
        }

        impl<'a> std::fmt::Debug for $name<'a> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({:p}{})", stringify!($name), self.as_ref(), if self.is_local() { ",L" } else { "" })
            }
        }
    };
}

tagged_ptr!(StringPtr, CowStr<'a>);
tagged_ptr!(NamePtr, Name<'a>);
tagged_ptr!(LevelPtr, Level<'a>);
tagged_ptr!(ExprPtr, Expr<'a>);
tagged_ptr!(BigUintPtr, BigUint);

// Compile-time guarantee that the low bit is free for tagging (low-bit encoding only;
// the `top-byte-ignore` encoding tags the top byte and needs no alignment guarantee).
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<Expr<'static>>() >= 2);
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<Name<'static>>() >= 2);
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<Level<'static>>() >= 2);
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<CowStr<'static>>() >= 2);
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<BigUint>() >= 2);
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<LevelPtr<'static>>() >= 2);

/// An interned sequence of `Level` pointers (the universe parameters of a
/// `Const`), stored as a tagged fat pointer into an arena.
pub struct LevelsPtr<'a> {
    ptr: NonNull<LevelPtr<'a>>,
    len: usize,
    _ph: PhantomData<&'a [LevelPtr<'a>]>,
}

impl<'a> Clone for LevelsPtr<'a> {
    #[inline]
    fn clone(&self) -> Self { *self }
}
impl<'a> Copy for LevelsPtr<'a> {}
unsafe impl<'a> Send for LevelsPtr<'a> {}
unsafe impl<'a> Sync for LevelsPtr<'a> {}

impl<'a> LevelsPtr<'a> {
    #[inline]
    pub(crate) fn global(s: &'a [LevelPtr<'a>]) -> Self {
        let ptr = unsafe { NonNull::new_unchecked(s.as_ptr() as *mut LevelPtr<'a>) };
        Self { ptr, len: s.len(), _ph: PhantomData }
    }
    #[inline]
    pub(crate) fn local(s: &'a [LevelPtr<'a>]) -> Self {
        let raw = (s.as_ptr() as *mut LevelPtr<'a>).map_addr(|a| a | PTR_TAG);
        Self { ptr: unsafe { NonNull::new_unchecked(raw) }, len: s.len(), _ph: PhantomData }
    }
    #[inline]
    pub(crate) fn is_local(self) -> bool { self.ptr.as_ptr().addr() & PTR_TAG != 0 }
    #[cfg(feature = "top-byte-ignore")]
    #[inline]
    pub(crate) fn as_ref(self) -> &'a [LevelPtr<'a>] {
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
    #[cfg(not(feature = "top-byte-ignore"))]
    #[inline]
    pub(crate) fn as_ref(self) -> &'a [LevelPtr<'a>] {
        let p = self.ptr.as_ptr().map_addr(|a| a & !PTR_TAG);
        unsafe { std::slice::from_raw_parts(p, self.len) }
    }
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn get_hash(&self) -> u64 { self.ptr.as_ptr().addr() as u64 }
}

impl<'a> std::ops::Deref for LevelsPtr<'a> {
    type Target = [LevelPtr<'a>];
    #[inline]
    fn deref(&self) -> &[LevelPtr<'a>] { self.as_ref() }
}
impl<'a> PartialEq for LevelsPtr<'a> {
    #[inline]
    fn eq(&self, o: &Self) -> bool { self.ptr.as_ptr().addr() == o.ptr.as_ptr().addr() && self.len == o.len }
}
impl<'a> Eq for LevelsPtr<'a> {}
impl<'a> std::hash::Hash for LevelsPtr<'a> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.ptr.as_ptr().addr() as u64) }
}
impl<'a> std::fmt::Debug for LevelsPtr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "LevelsPtr({:?})", self.as_ref()) }
}

// --------------------------------------------------------------------------
// Hash-cons interners.
//
// Each interner stores canonical `&'a T` references in a `hashbrown::HashTable`
// keyed by `T`'s structural hash, with shallow (address-based) structural
// equality. A lookup with a probe whose lifetime `'b` is no longer than `'a`
// coerces stored `&'a T` down to `&'b T` for comparison ("meet to the local
// lifetime"), enabling cross-arena dedup with no overhead.
// --------------------------------------------------------------------------

macro_rules! interner {
    ($name:ident, $pointee:ident) => {
        pub(crate) struct $name<'a> {
            table: HashTable<&'a $pointee<'a>>,
        }
        impl<'a> $name<'a> {
            fn new() -> Self { Self { table: HashTable::new() } }
            #[allow(dead_code)]
            pub(crate) fn len(&self) -> usize { self.table.len() }

            /// Probe by a value whose lifetime `'b` is no longer than `'a`.
            pub(crate) fn get<'b>(&self, v: &$pointee<'b>) -> Option<&'a $pointee<'a>>
            where
                'a: 'b, {
                let hash = v.struct_hash();
                self.table
                    .find(hash, |stored| {
                        let s: &$pointee<'b> = stored;
                        s == v
                    })
                    .copied()
            }

            /// Allocate a fresh value (assumed absent) and record it.
            pub(crate) fn insert(&mut self, arena: &ArenaRef<'a>, v: $pointee<'a>) -> &'a $pointee<'a> {
                let hash = v.struct_hash();
                let r: &'a $pointee<'a> = arena.alloc(v);
                self.table.insert_unique(hash, r, |s| s.struct_hash());
                r
            }

            /// get-or-insert; dedups within this arena (used by the parser).
            #[allow(dead_code)]
            pub(crate) fn intern(&mut self, arena: &ArenaRef<'a>, v: $pointee<'a>) -> &'a $pointee<'a> {
                if let Some(r) = self.get(&v) {
                    return r;
                }
                self.insert(arena, v)
            }
        }
    };
}

interner!(NameInterner, Name);
interner!(LevelInterner, Level);
interner!(ExprInterner, Expr);
interner!(StringInterner, CowStr);

pub(crate) struct BigUintInterner<'a> {
    table: HashTable<&'a BigUint>,
}
impl<'a> BigUintInterner<'a> {
    fn new() -> Self { Self { table: HashTable::new() } }
    pub(crate) fn get(&self, v: &BigUint) -> Option<&'a BigUint> {
        let hash = v.struct_hash();
        self.table.find(hash, |stored| **stored == *v).copied()
    }
    pub(crate) fn insert(&mut self, arena: &ArenaRef<'a>, v: BigUint) -> &'a BigUint {
        let hash = v.struct_hash();
        let r: &'a BigUint = arena.alloc(v);
        self.table.insert_unique(hash, r, |s| s.struct_hash());
        r
    }
    pub(crate) fn intern(&mut self, arena: &ArenaRef<'a>, v: BigUint) -> &'a BigUint {
        if let Some(r) = self.get(&v) {
            return r;
        }
        self.insert(arena, v)
    }
}

pub(crate) struct LevelsInterner<'a> {
    table: HashTable<&'a [LevelPtr<'a>]>,
}
impl<'a> LevelsInterner<'a> {
    fn new() -> Self { Self { table: HashTable::new() } }
    pub(crate) fn get<'b>(&self, v: &[LevelPtr<'b>]) -> Option<&'a [LevelPtr<'a>]>
    where
        'a: 'b, {
        let hash = v.struct_hash();
        self.table
            .find(hash, |stored| {
                let s: &[LevelPtr<'b>] = stored;
                s == v
            })
            .copied()
    }
    pub(crate) fn intern(&mut self, arena: &ArenaRef<'a>, v: &[LevelPtr<'a>]) -> &'a [LevelPtr<'a>] {
        if let Some(r) = self.get(v) {
            return r;
        }
        let hash = v.struct_hash();
        let r: &'a [LevelPtr<'a>] = arena.alloc_slice_copy(v);
        self.table.insert_unique(hash, r, |s| s.struct_hash());
        r
    }
}

/// The interning storage for one arena (global or local).
pub struct Dag<'a> {
    pub(crate) names: NameInterner<'a>,
    pub(crate) levels: LevelInterner<'a>,
    pub(crate) exprs: ExprInterner<'a>,
    pub(crate) uparams: LevelsInterner<'a>,
    pub(crate) strings: StringInterner<'a>,
    pub(crate) bignums: Option<BigUintInterner<'a>>,
}

impl<'a> Dag<'a> {
    pub(crate) fn new(config: &Config) -> Self {
        Self {
            names: NameInterner::new(),
            levels: LevelInterner::new(),
            exprs: ExprInterner::new(),
            uparams: LevelsInterner::new(),
            strings: StringInterner::new(),
            bignums: if config.nat_extension { Some(BigUintInterner::new()) } else { None },
        }
    }
}

fn is_expr_local_only(e: &Expr<'_>) -> bool {
    match *e {
        Expr::StringLit { ptr, .. } => ptr.is_local(),
        Expr::NatLit { ptr, .. } => ptr.is_local(),
        Expr::Proj { ty_name, structure, .. } => ty_name.is_local() || structure.is_local(),
        Expr::Var { .. } => false,
        Expr::Sort { level, .. } => level.is_local(),
        Expr::Const { name, levels, .. } => name.is_local() || levels.is_local(),
        Expr::App { fun, arg, .. } => fun.is_local() || arg.is_local(),
        Expr::Pi { binder_name, binder_type, body, .. } =>
            binder_name.is_local() || binder_type.is_local() || body.is_local(),
        Expr::Lambda { binder_name, binder_type, body, .. } =>
            binder_name.is_local() || binder_type.is_local() || body.is_local(),
        Expr::Let { binder_name, binder_type, val, body, .. } =>
            binder_name.is_local() || binder_type.is_local() || val.is_local() || body.is_local(),
        Expr::Local { .. } => true,
    }
}

pub(crate) fn new_fx_index_map<K, V>() -> FxIndexMap<K, V> { FxIndexMap::with_hasher(Default::default()) }

pub(crate) fn new_fx_hash_map<K, V>() -> FxHashMap<K, V> { FxHashMap::with_hasher(Default::default()) }

pub(crate) fn new_fx_hash_set<K>() -> FxHashSet<K> { FxHashSet::with_hasher(Default::default()) }

pub(crate) fn new_unique_hash_map<K, V>() -> UniqueHashMap<K, V> { UniqueHashMap::with_hasher(Default::default()) }

/// Convenience macro for creating a 64 bit hash.
#[macro_export]
macro_rules! hash64 {
    ( $( $x:expr ),* ) => {
        {
            use std::hash::{ Hash, Hasher };
            let mut hasher = rustc_hash::FxHasher::default();
            $(
                ($x).hash(&mut hasher);
            )*
            hasher.finish()
        }
    };
}

/// The implementation of natural number subtraction used in the kernel extension
/// for nat literals.
///
/// This is different from the subtraction defined for `BigUint` in that we saturate
/// at zero if y > x
pub(crate) fn nat_sub(x: BigUint, y: BigUint) -> BigUint {
    if y > x {
        BigUint::zero()
    } else {
        x - y
    }
}

/// The implementation of natural number division used in the kernel extension
/// for nat literals.
///
/// This is different from the division defined for `BigUint` in that division
/// by zero is an error for `BigUint`, but in Lean, it returns 0.
pub(crate) fn nat_div(x: BigUint, y: BigUint) -> BigUint {
    if y.is_zero() {
        BigUint::zero()
    } else {
        x / y
    }
}

/// The implementation of natural number mod used in the kernel extension
/// for nat literals.
pub(crate) fn nat_mod(x: BigUint, y: BigUint) -> BigUint {
    if y.is_zero() {
        x
    } else {
        x % y
    }
}

pub(crate) fn nat_gcd(x: &BigUint, y: &BigUint) -> BigUint { x.gcd(y) }

pub(crate) fn nat_xor(x: &BigUint, y: &BigUint) -> BigUint { x ^ y }

pub(crate) fn nat_shl(x: BigUint, y: BigUint) -> BigUint { x * BigUint::from(2u8).pow(y) }

pub(crate) fn nat_shr(x: BigUint, y: BigUint) -> BigUint { x / BigUint::from(2u8).pow(y) }

pub(crate) fn nat_land(x: BigUint, y: BigUint) -> BigUint { x & y }
pub(crate) fn nat_lor(x: BigUint, y: BigUint) -> BigUint { x | y }

pub struct ExprCache<'t> {
    /// Caches (e, offset) |-> output for instantiation. This cache is reset
    /// before every new call to `inst`, so there's no need to cache the sequence
    /// of substitutions.
    pub(crate) inst_cache: FxHashMap<(ExprPtr<'t>, u16), ExprPtr<'t>>,
    /// Caches (e, ks, vs) |-> output for level substitution.
    pub(crate) subst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    pub(crate) dsubst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    /// Caches (e, offset) |-> output for abstraction (re-binding free variables).
    /// This cache is reset before every new call to `inst`, so there's no need to
    /// cache the sequence of free variables.
    pub(crate) abstr_cache: FxHashMap<(ExprPtr<'t>, u16), ExprPtr<'t>>,
    /// A cache for (expr, starting deBruijn level, current deBruijn level)
    pub(crate) abstr_cache_levels: FxHashMap<(ExprPtr<'t>, u16, u16), ExprPtr<'t>>,
    pub(crate) simplify_cache: FxHashMap<LevelPtr<'t>, LevelPtr<'t>>,
}

impl<'t> ExprCache<'t> {
    fn new() -> Self {
        Self {
            inst_cache: new_fx_hash_map(),
            abstr_cache: new_fx_hash_map(),
            subst_cache: new_fx_hash_map(),
            dsubst_cache: new_fx_hash_map(),
            abstr_cache_levels: new_fx_hash_map(),
            simplify_cache: new_fx_hash_map(),
        }
    }
}

pub struct ExportFile<'p> {
    /// The interning storage for `Name`, `Level`, and `Expr` items (and strings,
    /// bignums, level-slices) read from the export file. This borrows the global
    /// arena, which is owned by the caller and outlives the `ExportFile`.
    pub(crate) dag: Dag<'p>,
    /// The anonymous name and level zero, which the export format back-references
    /// as the 0th item of their kind.
    pub(crate) anon: NamePtr<'p>,
    pub(crate) zero: LevelPtr<'p>,
    /// Declarations from the export file
    pub declars: DeclarMap<'p>,
    /// Notations from the export file
    pub notations: NotationMap<'p>,
    /// Cached names for convenience (`Quot`, `Nat`, etc.)
    pub name_cache: NameCache<'p>,
    pub config: Config,
    // Information used for setting EnvLimit during inductive checking.
    pub mutual_block_sizes: FxHashMap<NamePtr<'p>, (usize, usize)>,
}

impl<'p> ExportFile<'p> {
    pub fn new_env(&self, env_limit: EnvLimit<'p>) -> Env<'_, '_> {
        Env::new(&self.declars, &self.notations, env_limit)
    }

    pub fn with_ctx<F, A>(&self, f: F) -> A
    where
        F: FnOnce(&mut TcCtx<'_, 'p>) -> A, {
        let mut arena = Arena::new();
        arena.with_scope(|scope| {
            let mut ctx = TcCtx::new(self, scope);
            f(&mut ctx)
        })
    }

    pub fn with_tc<F, A>(&self, env_limit: EnvLimit<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        let mut arena = Arena::new();
        arena.with_scope(|scope| {
            let mut ctx = TcCtx::new(self, scope);
            let varena = ctx.arena;
            let env = self.new_env(env_limit);
            let mut tc = TypeChecker::new(&mut ctx, &env, varena, None);
            f(&mut tc)
        })
    }

    pub fn with_tc_and_declar<F, A>(&self, d: crate::env::DeclarInfo<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        let mut arena = Arena::new();
        arena.with_scope(|scope| {
            let mut ctx = TcCtx::new(self, scope);
            let varena = ctx.arena;
            let env = self.new_env(EnvLimit::ByName(d.name));
            let mut tc = TypeChecker::new(&mut ctx, &env, varena, Some(d));
            f(&mut tc)
        })
    }

    pub fn with_pp<F, A>(&self, f: F) -> A
    where
        F: FnOnce(&mut PrettyPrinter<'_, '_, 'p>) -> A, {
        self.with_ctx(|ctx| ctx.with_pp(f))
    }
}

/// A structure representing the memory context used for an individual `TypeChecker`.
pub struct TcCtx<'t, 'p> {
    /// Each type checker's context shares an immutable reference to the structured contents of
    /// the export file, and some additional information taken from the export file.
    pub(crate) export_file: &'t ExportFile<'p>,
    /// The local bump arena (a scope of the per-thread arena) into which temporary
    /// `Name`, `Level`, and `Expr` items created while type checking a declaration
    /// are allocated. The whole scope is reverted once the declaration is verified.
    pub(crate) arena: &'t ArenaRef<'t>,
    /// The interning tables for the local arena.
    pub(crate) dag: Dag<'t>,
    /// Non-monotonic counter showing the current deBruijn level (which is also the number
    /// of binders that are open above us). When a binder is opened and traversed under, this
    /// counter is incremented. When the binder is closed again, this counter is decremented.
    pub(crate) dbj_level_counter: u16,
    /// Monotonically increasing counter for unique free variables. Any two free variables created
    /// with the `mk_unique` constructor are unique within their `(ExportFile, TcCtx)` pair.
    pub(crate) unique_counter: u32,
    /// A cache for instantiation, free variable abstraction, and level substitution
    pub(crate) expr_cache: ExprCache<'t>,
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub fn new(export_file: &'t ExportFile<'p>, arena: &'t ArenaRef<'t>) -> Self {
        let dag = Dag::new(&export_file.config);
        Self { export_file, arena, dag, dbj_level_counter: 0u16, unique_counter: 0u32, expr_cache: ExprCache::new() }
    }

    pub fn with_tc<F, A>(&mut self, env_limit: EnvLimit<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let arena = self.arena;
        let env = self.export_file.new_env(env_limit);
        let mut tc = TypeChecker::new(self, &env, arena, None);
        f(&mut tc)
    }

    pub fn with_tc_and_env_ext<'x, F, A>(&mut self, env_ext: &'x DeclarMap<'t>, env_limit: EnvLimit<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let arena = self.arena;
        let env = crate::env::Env::new_w_temp_ext(
            &self.export_file.declars,
            Some(env_ext),
            &self.export_file.notations,
            env_limit,
        );
        let mut tc = TypeChecker::new(self, &env, arena, None);
        f(&mut tc)
    }

    pub fn with_pp<F, A>(&mut self, f: F) -> A
    where
        F: FnOnce(&mut PrettyPrinter<'_, 't, 'p>) -> A, {
        f(&mut PrettyPrinter::new(self))
    }

    pub fn read_name(&self, p: NamePtr<'t>) -> Name<'t> { *p.as_ref() }

    /// Convenience function for reading two items as a tuple.
    pub fn read_name_pr(&self, p: NamePtr<'t>, q: NamePtr<'t>) -> (Name<'t>, Name<'t>) {
        (self.read_name(p), self.read_name(q))
    }

    pub fn read_level(&self, p: LevelPtr<'t>) -> Level<'t> { *p.as_ref() }

    /// Convenience function for reading two items as a tuple.
    pub fn read_level_pair(&self, a: LevelPtr<'t>, x: LevelPtr<'t>) -> (Level<'t>, Level<'t>) {
        (self.read_level(a), self.read_level(x))
    }

    pub fn read_expr(&self, p: ExprPtr<'t>) -> Expr<'t> { *p.as_ref() }

    #[inline]
    pub fn read_expr_ref(&self, p: ExprPtr<'t>) -> &'t Expr<'t> { p.as_ref() }

    /// Convenience function for reading two items as a tuple.
    pub fn read_expr_pair(&self, a: ExprPtr<'t>, x: ExprPtr<'t>) -> (Expr<'t>, Expr<'t>) {
        (self.read_expr(a), self.read_expr(x))
    }

    pub fn read_string(&self, p: StringPtr<'t>) -> &'t CowStr<'t> { p.as_ref() }

    pub fn read_bignum(&self, p: BigUintPtr<'t>) -> Option<&'t BigUint> { Some(p.as_ref()) }

    pub fn read_levels(&self, p: LevelsPtr<'t>) -> &'t [LevelPtr<'t>] { p.as_ref() }

    /// Store a `Name`, getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived (global) storage first.
    pub fn alloc_name(&mut self, n: Name<'t>) -> NamePtr<'t> {
        if let Some(r) = self.export_file.dag.names.get(&n) {
            return NamePtr::global(r);
        }
        NamePtr::local(self.dag.names.intern(self.arena, n))
    }

    /// Store a `Level`, getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived (global) storage first.
    pub fn alloc_level(&mut self, l: Level<'t>) -> LevelPtr<'t> {
        if let Some(r) = self.export_file.dag.levels.get(&l) {
            return LevelPtr::global(r);
        }
        LevelPtr::local(self.dag.levels.intern(self.arena, l))
    }

    /// Store an `Expr`, getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Probes the local cache first, then (unless the expr is local-only) the
    /// global cache, matching the historical interning policy.
    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        if let Some(r) = self.dag.exprs.get(&e) {
            return ExprPtr::local(r);
        }
        if !is_expr_local_only(&e) {
            if let Some(r) = self.export_file.dag.exprs.get(&e) {
                return ExprPtr::global(r);
            }
        }
        ExprPtr::local(self.dag.exprs.insert(self.arena, e))
    }

    /// Store a string (a `CowStr`), getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived (global) storage first.
    pub(crate) fn alloc_string(&mut self, s: CowStr<'t>) -> StringPtr<'t> {
        if let Some(r) = self.export_file.dag.strings.get(&s) {
            return StringPtr::global(r);
        }
        StringPtr::local(self.dag.strings.intern(self.arena, s))
    }

    /// Store a `BigUint` (a bignum), getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived (global) storage first.
    ///
    /// Used for Nat literals.
    pub(crate) fn alloc_bignum(&mut self, n: BigUint) -> Option<BigUintPtr<'t>> {
        if let Some(global) = self.export_file.dag.bignums.as_ref() {
            if let Some(r) = global.get(&n) {
                return Some(BigUintPtr::global(r));
            }
        }
        let local = self.dag.bignums.as_mut()?;
        Some(BigUintPtr::local(local.intern(self.arena, n)))
    }

    /// Store a sequence of `Level` items, getting back a pointer to the allocated sequence.
    /// If the sequence was already stored, return a pointer to the previously inserted sequence.
    /// Checks the longer-lived (global) storage first.
    pub fn alloc_levels(&mut self, ls: &[LevelPtr<'t>]) -> LevelsPtr<'t> {
        if let Some(r) = self.export_file.dag.uparams.get(ls) {
            return LevelsPtr::global(r);
        }
        LevelsPtr::local(self.dag.uparams.intern(self.arena, ls))
    }

    /// Store a sequence of `Level` items, probing with a slice. Identical to
    /// `alloc_levels` now that levels are stored as arena slices.
    pub fn alloc_levels_slice(&mut self, ls: &[LevelPtr<'t>]) -> LevelsPtr<'t> { self.alloc_levels(ls) }

    /// A constructor for the anonymous name.
    pub fn anonymous(&self) -> NamePtr<'t> { self.export_file.anon }

    pub fn str(&mut self, pfx: NamePtr<'t>, sfx: StringPtr<'t>) -> NamePtr<'t> {
        let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
        self.alloc_name(Name::Str(pfx, sfx, hash))
    }

    pub fn str1_owned(&mut self, s: String) -> NamePtr<'t> {
        let anon = self.alloc_name(Name::Anon);
        let s = self.alloc_string(CowStr::Owned(s));
        self.str(anon, s)
    }

    pub fn str1(&mut self, s: &'static str) -> NamePtr<'t> {
        let anon = self.alloc_name(Name::Anon);
        let s = self.alloc_string(CowStr::Borrowed(s));
        self.str(anon, s)
    }

    pub fn str2(&mut self, s1: &'static str, s2: &'static str) -> NamePtr<'t> {
        let s1 = self.alloc_string(CowStr::Borrowed(s1));
        let s2 = self.alloc_string(CowStr::Borrowed(s2));
        let n = self.anonymous();
        let n = self.str(n, s1);
        self.str(n, s2)
    }

    pub fn zero(&self) -> LevelPtr<'t> { self.export_file.zero }

    pub fn num(&mut self, pfx: NamePtr<'t>, sfx: u64) -> NamePtr<'t> {
        let hash = hash64!(crate::name::NUM_HASH, pfx, sfx);
        self.alloc_name(Name::Num(pfx, sfx, hash))
    }

    pub fn succ(&mut self, l: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::SUCC_HASH, l);
        self.alloc_level(Level::Succ(l, hash))
    }

    pub fn max(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::MAX_HASH, l, r);
        self.alloc_level(Level::Max(l, r, hash))
    }
    pub fn imax(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::IMAX_HASH, l, r);
        self.alloc_level(Level::IMax(l, r, hash))
    }
    pub fn param(&mut self, n: NamePtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::PARAM_HASH, n);
        self.alloc_level(Level::Param(n, hash))
    }

    pub fn mk_var(&mut self, dbj_idx: u16) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::VAR_HASH, dbj_idx);
        self.alloc_expr(Expr::Var { dbj_idx, hash })
    }

    pub fn mk_sort(&mut self, level: LevelPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::SORT_HASH, level);
        self.alloc_expr(Expr::Sort { level, hash })
    }

    pub fn mk_const(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::CONST_HASH, name, levels);
        self.alloc_expr(Expr::Const { name, levels, hash })
    }

    pub fn mk_app(&mut self, fun: ExprPtr<'t>, arg: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::APP_HASH, fun, arg);
        let num_loose_bvars = self.num_loose_bvars(fun).max(self.num_loose_bvars(arg));
        let has_fvars = self.has_fvars(fun) || self.has_fvars(arg);
        self.alloc_expr(Expr::App { fun, arg, num_loose_bvars, has_fvars, hash })
    }

    pub fn mk_lambda(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_style, binder_type, body);
        let num_loose_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
        let has_fvars = self.has_fvars(binder_type) || self.has_fvars(body);
        self.alloc_expr(Expr::Lambda { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash })
    }

    pub fn mk_pi(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_style, binder_type, body);
        let num_loose_bvars = self.num_loose_bvars(binder_type).max(self.num_loose_bvars(body).saturating_sub(1));
        let has_fvars = self.has_fvars(binder_type) || self.has_fvars(body);
        self.alloc_expr(Expr::Pi { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash })
    }

    pub fn mk_let(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        nondep: bool,
    ) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body, nondep);
        let num_loose_bvars = self
            .num_loose_bvars(binder_type)
            .max(self.num_loose_bvars(val).max(self.num_loose_bvars(body).saturating_sub(1)));
        let has_fvars = self.has_fvars(binder_type) || self.has_fvars(val) || self.has_fvars(body);
        self.alloc_expr(Expr::Let { binder_name, binder_type, val, body, num_loose_bvars, has_fvars, hash, nondep })
    }

    pub fn mk_proj(&mut self, ty_name: NamePtr<'t>, idx: usize, structure: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, structure);
        let num_loose_bvars = self.num_loose_bvars(structure);
        let has_fvars = self.has_fvars(structure);
        self.alloc_expr(Expr::Proj { ty_name, idx, structure, num_loose_bvars, has_fvars, hash })
    }

    pub fn mk_string_lit(&mut self, string_ptr: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.string_extension {
            return None
        }
        let hash = hash64!(crate::expr::STRING_LIT_HASH, string_ptr);
        Some(self.alloc_expr(Expr::StringLit { ptr: string_ptr, hash }))
    }

    pub fn mk_string_lit_quick(&mut self, s: CowStr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.string_extension {
            return None
        }
        let string_ptr = self.alloc_string(s);
        self.mk_string_lit(string_ptr)
    }

    pub fn mk_nat_lit(&mut self, num_ptr: BigUintPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.nat_extension {
            return None
        }
        let hash = hash64!(crate::expr::NAT_LIT_HASH, num_ptr);
        Some(self.alloc_expr(Expr::NatLit { ptr: num_ptr, hash }))
    }

    /// Shortcut to make an `Expr::NatLit` directly from a `BigUint`, rather than
    /// going `alloc_bignum` and `mk_nat_lit`
    pub fn mk_nat_lit_quick(&mut self, n: BigUint) -> Option<ExprPtr<'t>> {
        let num_ptr = self.alloc_bignum(n)?;
        self.mk_nat_lit(num_ptr)
    }

    /// Construct a free variable expression representing a deBruijn level, and
    /// increment the context's counter.
    pub fn mk_dbj_level(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let level = self.dbj_level_counter;
        self.dbj_level_counter += 1;
        let id = FVarId::DbjLevel(level);
        let hash = hash64!(crate::expr::LOCAL_HASH, binder_name, binder_style, binder_type, id);
        self.alloc_expr(Expr::Local { binder_name, binder_style, binder_type, id, hash })
    }

    /// Construct a free variable expression representing a deBruijn level, reusing
    /// a particular level counter, and without incrementing the context's counter for
    /// open binders.
    pub fn remake_dbj_level(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        level: u16,
    ) -> ExprPtr<'t> {
        let id = FVarId::DbjLevel(level);
        let hash = hash64!(crate::expr::LOCAL_HASH, binder_name, binder_style, binder_type, id);
        self.alloc_expr(Expr::Local { binder_name, binder_style, binder_type, id, hash })
    }

    /// Construct a free variable with a unique ID, incrementing the monotonic counter
    /// for unique free variable identifiers.
    pub fn mk_unique(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let unique_id = self.unique_counter;
        self.unique_counter += 1;
        let id = FVarId::Unique(unique_id);
        let hash = hash64!(crate::expr::LOCAL_HASH, binder_name, binder_style, binder_type, id);
        self.alloc_expr(Expr::Local { binder_name, binder_style, binder_type, id, hash })
    }

    /// "replace" a free variable when closing a binder, decrementing the deBruijn level
    /// counter, so that level can be reused as appropriate.
    pub(crate) fn replace_dbj_level(&mut self, e: ExprPtr<'t>) {
        match self.read_expr(e) {
            Expr::Local { id: FVarId::DbjLevel(level), .. } => {
                debug_assert_eq!(level + 1, self.dbj_level_counter);
                self.dbj_level_counter -= 1;
            }
            _ => panic!("replace_dbj_level didn't get a Local, got {:?}", self.debug_print(e)),
        }
    }

    /// Convert the deBruijn level of a free variable to a deBruijn index for a bound
    /// variable. This is the same thing as asking "if this element is the `nth` element
    /// when counting from the front of a sequence of length `m`, what is its position
    /// when counting from the back?"
    pub(crate) fn fvar_to_bvar(&mut self, num_open_binders: u16, dbj_level: u16) -> ExprPtr<'t> {
        self.mk_var((num_open_binders - dbj_level) - 1)
    }
}

impl<'a> StringInterner<'a> {
    /// Content-based lookup used when building the name cache (probe lifetime is
    /// unrelated to the arena lifetime, so we compare by `&str` directly).
    pub(crate) fn get_str(&self, s: &str) -> Option<&'a CowStr<'a>> {
        let hash = s.struct_hash();
        self.table.find(hash, |stored| stored.as_ref() == s).copied()
    }
}

impl<'a> Dag<'a> {
    /// Used for constructing the name cache; probes the interned strings by content.
    fn get_string_ptr(&self, s: &str) -> Option<StringPtr<'a>> { self.strings.get_str(s).map(StringPtr::global) }

    // Find e.g. `Quot.lift` from "Quot.lift", starting from the anonymous name.
    fn find_name(&self, anon: NamePtr<'a>, dot_separated_name: &str) -> Option<NamePtr<'a>> {
        let mut pfx = anon;
        for s in dot_separated_name.split('.') {
            if let Ok(num) = s.parse::<u64>() {
                let hash = hash64!(crate::name::NUM_HASH, pfx, num);
                if let Some(r) = self.names.get(&Name::Num(pfx, num, hash)) {
                    pfx = NamePtr::global(r);
                    continue
                }
            } else if let Some(sfx) = self.get_string_ptr(s) {
                let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
                if let Some(r) = self.names.get(&Name::Str(pfx, sfx, hash)) {
                    pfx = NamePtr::global(r);
                    continue
                }
            }
            return None
        }
        Some(pfx)
    }

    /// If these names are present in the export file, we want to cache
    /// them since we need to retrieve them quite frequently.
    pub(crate) fn mk_name_cache(&self, anon: NamePtr<'a>) -> NameCache<'a> {
        NameCache {
            quot: self.find_name(anon, "Quot"),
            quot_mk: self.find_name(anon, "Quot.mk"),
            quot_lift: self.find_name(anon, "Quot.lift"),
            quot_ind: self.find_name(anon, "Quot.ind"),
            string: self.find_name(anon, "String"),
            string_of_list: self.find_name(anon, "String.ofList"),
            nat: self.find_name(anon, "Nat"),
            nat_zero: self.find_name(anon, "Nat.zero"),
            nat_succ: self.find_name(anon, "Nat.succ"),
            nat_add: self.find_name(anon, "Nat.add"),
            nat_sub: self.find_name(anon, "Nat.sub"),
            nat_mul: self.find_name(anon, "Nat.mul"),
            nat_pow: self.find_name(anon, "Nat.pow"),
            nat_mod: self.find_name(anon, "Nat.mod"),
            nat_div: self.find_name(anon, "Nat.div"),
            nat_div_go: self.find_name(anon, "Nat.div.go"),
            nat_mod_core_go: self.find_name(anon, "Nat.modCore.go"),
            nat_beq: self.find_name(anon, "Nat.beq"),
            nat_ble: self.find_name(anon, "Nat.ble"),
            nat_gcd: self.find_name(anon, "Nat.gcd"),
            nat_xor: self.find_name(anon, "Nat.xor"),
            nat_land: self.find_name(anon, "Nat.land"),
            nat_lor: self.find_name(anon, "Nat.lor"),
            nat_shl: self.find_name(anon, "Nat.shiftLeft"),
            nat_shr: self.find_name(anon, "Nat.shiftRight"),
            bool_true: self.find_name(anon, "Bool.true"),
            bool_false: self.find_name(anon, "Bool.false"),
            char: self.find_name(anon, "Char"),
            char_of_nat: self.find_name(anon, "Char.ofNat"),
            list: self.find_name(anon, "List"),
            list_nil: self.find_name(anon, "List.nil"),
            list_cons: self.find_name(anon, "List.cons"),
        }
    }
}

/// This just caches common names; the values are `Some(x)` if the name
/// is present in the export file, otherwise they're `None`.
#[derive(Debug, Clone, Copy)]
pub struct NameCache<'p> {
    pub(crate) quot: Option<NamePtr<'p>>,
    pub(crate) quot_mk: Option<NamePtr<'p>>,
    pub(crate) quot_lift: Option<NamePtr<'p>>,
    pub(crate) quot_ind: Option<NamePtr<'p>>,
    pub(crate) nat: Option<NamePtr<'p>>,
    pub(crate) nat_zero: Option<NamePtr<'p>>,
    pub(crate) nat_succ: Option<NamePtr<'p>>,
    pub(crate) nat_add: Option<NamePtr<'p>>,
    pub(crate) nat_sub: Option<NamePtr<'p>>,
    pub(crate) nat_mul: Option<NamePtr<'p>>,
    pub(crate) nat_pow: Option<NamePtr<'p>>,
    pub(crate) nat_mod: Option<NamePtr<'p>>,
    pub(crate) nat_div: Option<NamePtr<'p>>,
    pub(crate) nat_div_go: Option<NamePtr<'p>>,
    pub(crate) nat_mod_core_go: Option<NamePtr<'p>>,
    pub(crate) nat_beq: Option<NamePtr<'p>>,
    pub(crate) nat_ble: Option<NamePtr<'p>>,
    pub(crate) nat_gcd: Option<NamePtr<'p>>,
    pub(crate) nat_xor: Option<NamePtr<'p>>,
    pub(crate) nat_land: Option<NamePtr<'p>>,
    pub(crate) nat_lor: Option<NamePtr<'p>>,
    pub(crate) nat_shr: Option<NamePtr<'p>>,
    pub(crate) nat_shl: Option<NamePtr<'p>>,
    pub(crate) string: Option<NamePtr<'p>>,
    pub(crate) string_of_list: Option<NamePtr<'p>>,
    pub(crate) bool_false: Option<NamePtr<'p>>,
    pub(crate) bool_true: Option<NamePtr<'p>>,
    pub(crate) char: Option<NamePtr<'p>>,
    pub(crate) char_of_nat: Option<NamePtr<'p>>,
    #[allow(dead_code)]
    pub(crate) list: Option<NamePtr<'p>>,
    pub(crate) list_nil: Option<NamePtr<'p>>,
    pub(crate) list_cons: Option<NamePtr<'p>>,
}

pub(crate) struct TcCache<'a, 't> {
    pub(crate) infer_cache_check: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) infer_cache_no_check: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) whnf_cache: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) whnf_no_unfolding_cache: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) eq_cache: UnionFind<ExprPtr<'t>>,
    /// A cache of congruence failures during the lazy delta step procedure.
    /// Strong reduction is not used during type-checking, this is more of a library/inspection feature.
    pub(crate) strong_cache: UniqueHashMap<(ExprPtr<'t>, bool, bool), ExprPtr<'t>>,
    pub(crate) unfold_const_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) rec_rule_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) const_head_type_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) const_head_value_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) const_result_level_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), LevelPtr<'t>>,
    pub(crate) conv_cache: FxHashSet<(usize, usize)>,
    pub(crate) conv_cache_neg: FxHashSet<(usize, usize)>,
    pub(crate) conv_cache_neg_probe: FxHashSet<(usize, usize)>,
    pub(crate) probe_depth: u32,
    pub(crate) closed_eval_cache: FxHashMap<ExprPtr<'t>, V<'a>>,
    pub(crate) open_eval_cache: FxHashMap<(usize, ExprPtr<'t>), V<'a>>,
    pub(crate) open_eval_seen: FxHashSet<ExprPtr<'t>>,
    pub(crate) bvar_hc: FxHashMap<(u32, usize), V<'a>>,
    pub(crate) env_hc: FxHashMap<(usize, usize), E<'a>>,
    pub(crate) spine_hc: FxHashMap<(usize, u8, u64, u64), S<'a>>,
    pub(crate) lam_hc: FxHashMap<(ExprPtr<'t>, usize, ExprPtr<'t>), V<'a>>,
    pub(crate) pi_hc: FxHashMap<(usize, usize, ExprPtr<'t>), V<'a>>,
    pub(crate) rigid_hc: FxHashMap<(u8, u64, u64, usize), V<'a>>,
    pub(crate) unfold_hc: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>, usize, usize), V<'a>>,
    pub(crate) iota_stuck: FxHashSet<usize>,
    pub(crate) struct_eta_cache: FxHashMap<(usize, NamePtr<'t>), Option<V<'a>>>,
    pub(crate) iota_cache: FxHashMap<usize, V<'a>>,
    pub(crate) canon_cache: FxHashMap<usize, V<'a>>,
    pub(crate) content_hc: FxHashMap<(u8, u64), V<'a>>,
    pub(crate) fvar_cache: FxHashMap<usize, bool>,
}

impl<'a, 't> TcCache<'a, 't> {
    pub(crate) fn new() -> Self {
        Self {
            infer_cache_check: new_unique_hash_map(),
            infer_cache_no_check: new_unique_hash_map(),
            whnf_cache: new_unique_hash_map(),
            whnf_no_unfolding_cache: new_unique_hash_map(),
            eq_cache: UnionFind::new(),
            strong_cache: new_unique_hash_map(),
            unfold_const_cache: new_fx_hash_map(),
            rec_rule_cache: new_fx_hash_map(),
            const_head_type_cache: new_fx_hash_map(),
            const_head_value_cache: new_fx_hash_map(),
            const_result_level_cache: new_fx_hash_map(),
            conv_cache: new_fx_hash_set(),
            conv_cache_neg: new_fx_hash_set(),
            conv_cache_neg_probe: new_fx_hash_set(),
            probe_depth: 0,
            closed_eval_cache: new_fx_hash_map(),
            open_eval_cache: new_fx_hash_map(),
            open_eval_seen: new_fx_hash_set(),
            bvar_hc: new_fx_hash_map(),
            env_hc: new_fx_hash_map(),
            spine_hc: new_fx_hash_map(),
            lam_hc: new_fx_hash_map(),
            pi_hc: new_fx_hash_map(),
            rigid_hc: new_fx_hash_map(),
            unfold_hc: new_fx_hash_map(),
            iota_stuck: new_fx_hash_set(),
            struct_eta_cache: new_fx_hash_map(),
            iota_cache: new_fx_hash_map(),
            canon_cache: new_fx_hash_map(),
            content_hc: new_fx_hash_map(),
            fvar_cache: new_fx_hash_map(),
        }
    }

    pub(crate) fn clear(&mut self) {
        self.infer_cache_check.clear();
        self.infer_cache_no_check.clear();
        self.whnf_cache.clear();
        self.whnf_no_unfolding_cache.clear();
        self.eq_cache.clear();
        self.strong_cache.clear();
        self.unfold_const_cache.clear();
        self.rec_rule_cache.clear();
        self.const_head_type_cache.clear();
        self.const_head_value_cache.clear();
        self.const_result_level_cache.clear();
        self.conv_cache.clear();
        self.conv_cache_neg.clear();
        self.conv_cache_neg_probe.clear();
        self.env_hc.clear();
        self.open_eval_cache.clear();
        self.open_eval_seen.clear();
        self.bvar_hc.clear();
        self.spine_hc.clear();
        self.lam_hc.clear();
        self.pi_hc.clear();
        self.rigid_hc.clear();
        self.unfold_hc.clear();
        self.iota_stuck.clear();
        self.struct_eta_cache.clear();
        self.iota_cache.clear();
        self.canon_cache.clear();
        self.content_hc.clear();
        self.fvar_cache.clear();
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct Config {
    /// The path to the export file to be checked (if `none`, users must specify `use_stdin: true`)
    pub export_file_path: Option<PathBuf>,

    /// A value indicating whether the type checker should look to stdin to receive the export file.
    #[serde(default)]
    pub use_stdin: bool,

    /// A list of the whitelisted axioms the user wants to allow.
    pub permitted_axioms: Option<Vec<String>>,

    /// A boolean indicating what behavior the typechecker should exhibit when encountering
    /// an axiom in an export file which has not explicitly been named in `permitted_axioms`.
    /// if `unpermitted_axiom_hard_error: true`, the typechecker will fail with a hard error.
    /// if `unpermitted_axiom_hard_error: false`, the typechecker will NOT add the axiom to the environment,
    /// and will continue typechecking in an environment that does not contain the disallowed axiom.
    #[serde(default = "default_true")]
    pub unpermitted_axiom_hard_error: bool,

    /// Number of threads to use for type checking.
    #[serde(default)]
    pub num_threads: usize,

    #[serde(default)]
    pub nat_extension: bool,
    #[serde(default)]
    pub string_extension: bool,

    /// A list of declaration names the user wants to be pretty-printed back to them on termination.
    pub pp_declars: Option<Vec<String>>,

    /// Indicates what the typechecker should do when it's been asked to pretty-print a declaration
    /// that is not actually in the environment. We give this option because that scenario is
    /// strongly indicative of a mismatch between what the user thinks is in the export file and
    /// what is actually in the export file.
    /// If `true`, the typechecker will fail with a hard error.
    /// If `false`, the typechecker will not fail just because of this.
    #[serde(default = "default_true")]
    pub unknown_pp_declar_hard_error: bool,

    #[serde(default)]
    pub pp_options: PpOptions,

    /// Optionally, a path to write the pretty-printer output to.
    pub pp_output_path: Option<PathBuf>,

    #[serde(default)]
    pub pp_to_stdout: bool,

    #[serde(default)]
    pub print_success_message: bool,

    /// If `true`, the typechecker will print the axioms actually admitted to the environment
    /// when typechecking is finished.
    #[serde(default = "default_true")]
    pub print_axioms: bool,

    /// If set to `true`, will allow all axioms to be admitted to the environment.
    /// This is checked so as to be mutually exclusive with any of the axiom allow list/whitelist features.
    #[serde(default)]
    pub unsafe_permit_all_axioms: bool,
}

impl TryFrom<&Path> for Config {
    type Error = Box<dyn Error>;
    fn try_from(p: &Path) -> Result<Config, Self::Error> {
        match OpenOptions::new().read(true).truncate(false).open(p) {
            Err(e) => Err(Box::from(format!("failed to open configuration file: {:?}", e))),
            Ok(config_file) => {
                let config = serde_json::from_reader::<_, Config>(BufReader::new(config_file)).unwrap();
                if config.export_file_path.is_none() && !config.use_stdin {
                    return Err(Box::from(format!(
                        "incompatible config options: must specify a path to an export file OR set `use_stdin: true`"
                    )))
                }
                if config.export_file_path.is_some() && config.use_stdin {
                    return Err(Box::from(format!(
                        "incompatible config options: if an export file path is given, `use_stdin` cannot be `true`"
                    )))
                }
                if config.unsafe_permit_all_axioms {
                    if config.unpermitted_axiom_hard_error {
                        return Err(Box::from(format!(
                            "incompatible config options: unsafe_permit_all_axioms && unpermitted_axioms_hard_error"
                        )))
                    }
                    if config.permitted_axioms.is_some() {
                        return Err(Box::from(format!(
                            "incompatible config options: unsafe_permit_all_axioms && nonempty permitted_axioms list"
                        )))
                    }
                }
                Ok(config)
            }
        }
    }
}

pub enum PpDestination {
    File(BufWriter<std::fs::File>),
    Stdout(BufWriter<std::io::Stdout>),
}

impl PpDestination {
    pub(crate) fn stdout() -> Self { Self::Stdout(BufWriter::new(std::io::stdout())) }
    pub(crate) fn write_line(&mut self, s: String, sep: &str) -> Result<usize, Box<dyn Error>> {
        match self {
            PpDestination::File(f) => f.write(s.as_bytes()).and_then(|_| f.write(sep.as_bytes())).map_err(Box::from),
            PpDestination::Stdout(f) => f.write(s.as_bytes()).and_then(|_| f.write(sep.as_bytes())).map_err(Box::from),
        }
    }
}

impl Config {
    pub fn get_pp_destination(&self) -> Result<Option<PpDestination>, Box<dyn Error>> {
        if let Some(pathbuf) = self.pp_output_path.as_ref() {
            match OpenOptions::new().write(true).truncate(false).open(pathbuf) {
                Ok(file) => Ok(Some(PpDestination::File(BufWriter::new(file)))),
                Err(e) => Err(Box::from(format!("Failed to open pretty printer destination file: {:?}", e))),
            }
        } else if self.pp_to_stdout {
            Ok(Some(PpDestination::stdout()))
        } else {
            Ok(None)
        }
    }

    // Returns the export file, and a list of strings representing the names of "skipped" axioms
    // (axioms which were in the export file, but not allowed by the execution config).
    //
    // The global arena (owned by the caller) backs all of the export file's interned
    // items, so it must outlive the returned `ExportFile`.
    pub fn to_export_file<'a>(self, arena: &'a ArenaRef<'a>) -> Result<(ExportFile<'a>, Vec<String>), Box<dyn Error>> {
        if let Some(pathbuf) = self.export_file_path.as_ref() {
            match OpenOptions::new().read(true).truncate(false).open(pathbuf) {
                Ok(file) => crate::parser::parse_export_file(arena, BufReader::new(file), self),
                Err(e) => Err(Box::from(format!("Failed to open export file: {:?}", e))),
            }
        } else if self.use_stdin {
            let reader = BufReader::new(std::io::stdin());
            crate::parser::parse_export_file(arena, reader, self)
        } else {
            panic!("Configuration file must specify en export file path or \"use_stdin\": true")
        }
    }
}

// The intent is to use this for reporting exit status/error info
// when we go back and get rid of all of the `panic!` invocations
// and use more involved error handling.
#[allow(dead_code)]
#[derive(Debug, Clone)]
struct ExitStatus {
    tc_err: Option<String>,
    pp_err: Option<String>,
}
