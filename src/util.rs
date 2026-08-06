use crate::env::{DeclarMap, Env, EnvLimit, NotationMap};
use crate::expr::{
    BinderStyle, Expr, APP_HASH, CONST_HASH, LAMBDA_HASH, LET_HASH, NAT_LIT_HASH, PI_HASH,
    PROJ_HASH, SORT_HASH, STRING_LIT_HASH, VAR_HASH,
};
use crate::level::{Level, IMAX_HASH, MAX_HASH, PARAM_HASH, SUCC_HASH};
use crate::name::{Name, NUM_HASH, STR_HASH};
use crate::parser::{parse_export_file, parse_export_mapped};
use crate::pretty_printer::{PpOptions, PrettyPrinter};
use crate::tc::TypeChecker;
use crate::value::{E, S, V};
use hashbrown::HashTable;
use indexmap::IndexMap;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::identities::Zero;
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

pub(crate) const STANDARD_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

#[derive(Debug)]
pub struct Decline(pub String);

impl std::fmt::Display for Decline {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "declined: {}", self.0) }
}

impl Error for Decline {}

pub(crate) fn decline<A>(msg: impl Into<String>) -> Result<A, Box<dyn Error>> { Err(Box::new(Decline(msg.into()))) }

pub(crate) type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;
pub(crate) type FxHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub(crate) type FxHashSet<K> = HashSet<K, BuildHasherDefault<FxHasher>>;

pub(crate) type CowStr<'a> = Cow<'a, str>;

#[cfg(all(feature = "top-byte-ignore", not(target_arch = "aarch64")))]
compile_error!("the `top-byte-ignore` feature requires the aarch64 target architecture (Top-Byte-Ignore)");

#[cfg(feature = "top-byte-ignore")]
const PTR_TAG: usize = 1 << 56;
#[cfg(not(feature = "top-byte-ignore"))]
const PTR_TAG: usize = 1;

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

pub(crate) trait RawHash {
    fn raw_hash(&self) -> u64;
}

impl RawHash for CowStr<'_> {
    #[inline]
    fn raw_hash(&self) -> u64 { self.struct_hash() }
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

        unsafe impl<'a> Send for $name<'a> {}
        unsafe impl<'a> Sync for $name<'a> {}

        impl<'a> $name<'a> {
            #[inline]
            pub(crate) fn global(r: &'a $pointee) -> Self {
                Self { ptr: NonNull::from(r), _ph: PhantomData }
            }

            #[inline]
            pub(crate) fn local(r: &'a $pointee) -> Self {
                let tagged = NonNull::from(r).as_ptr().map_addr(|a| a | PTR_TAG);
                Self { ptr: unsafe { NonNull::new_unchecked(tagged) }, _ph: PhantomData }
            }

            #[inline]
            pub(crate) fn is_local(self) -> bool { self.ptr.as_ptr().addr() & PTR_TAG != 0 }

            #[cfg(feature = "top-byte-ignore")]
            #[inline]
            pub(crate) fn as_ref(self) -> &'a $pointee { unsafe { &*self.ptr.as_ptr() } }
            #[cfg(not(feature = "top-byte-ignore"))]
            #[inline]
            pub(crate) fn as_ref(self) -> &'a $pointee {
                unsafe { &*self.ptr.as_ptr().map_addr(|a| a & !PTR_TAG) }
            }

            #[inline]
            #[allow(dead_code)]
            pub(crate) fn get_hash(&self) -> u64 { self.ptr.as_ptr().addr() as u64 }

            #[inline]
            #[allow(dead_code)]
            pub(crate) fn from_raw_hash(a: u64) -> Self {
                let p = std::ptr::without_provenance_mut::<$pointee>(a as usize);
                Self { ptr: unsafe { NonNull::new_unchecked(p) }, _ph: PhantomData }
            }
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
tagged_ptr!(NamePtr, crate::name::NameNode<'a>);
tagged_ptr!(LevelPtr, Level<'a>);
tagged_ptr!(BigUintPtr, BigUint);

const EXPR_ADDR_MASK: u64 = 0x0000_ffff_ffff_fff8;
const EXPR_LOCAL_BIT: u64 = 1;
const EXPR_BVAR_SHIFT: u32 = 48;

pub struct ExprPtr<'a> {
    bits: std::num::NonZeroU64,
    _ph: PhantomData<&'a Expr<'a>>,
}

impl<'a> Clone for ExprPtr<'a> {
    #[inline]
    fn clone(&self) -> Self { *self }
}
impl<'a> Copy for ExprPtr<'a> {}
unsafe impl<'a> Send for ExprPtr<'a> {}
unsafe impl<'a> Sync for ExprPtr<'a> {}

impl<'a> ExprPtr<'a> {
    #[inline]
    fn pack(r: &'a Expr<'a>, tag: u64) -> Self {
        let addr = r as *const Expr<'a> as usize as u64;
        debug_assert!(addr & !EXPR_ADDR_MASK == 0);
        let derived = u64::from(r.num_loose_bvars()) << EXPR_BVAR_SHIFT;
        Self { bits: unsafe { std::num::NonZeroU64::new_unchecked(addr | tag | derived) }, _ph: PhantomData }
    }

    #[inline]
    pub(crate) fn global(r: &'a Expr<'a>, num_loose_bvars: u16) -> Self {
        let addr = r as *const Expr<'a> as usize as u64;
        debug_assert!(addr & !EXPR_ADDR_MASK == 0);
        debug_assert_eq!(num_loose_bvars, r.num_loose_bvars());
        let bits = addr | (u64::from(num_loose_bvars) << EXPR_BVAR_SHIFT);
        Self { bits: unsafe { std::num::NonZeroU64::new_unchecked(bits) }, _ph: PhantomData }
    }

    #[inline]
    pub(crate) fn local(r: &'a Expr<'a>) -> Self { Self::pack(r, EXPR_LOCAL_BIT) }


    #[inline]
    pub(crate) fn is_local(self) -> bool { self.bits.get() & EXPR_LOCAL_BIT != 0 }

    #[inline]
    pub(crate) fn num_loose_bvars(self) -> u16 { (self.bits.get() >> EXPR_BVAR_SHIFT) as u16 }

    #[inline]
    pub(crate) fn as_ref(self) -> &'a Expr<'a> {
        unsafe { &*((self.bits.get() & EXPR_ADDR_MASK) as usize as *const Expr<'a>) }
    }
}

impl<'a> std::ops::Deref for ExprPtr<'a> {
    type Target = Expr<'a>;
    #[inline]
    fn deref(&self) -> &Expr<'a> { self.as_ref() }
}

impl<'a> PartialEq for ExprPtr<'a> {
    #[inline]
    fn eq(&self, o: &Self) -> bool { self.bits == o.bits }
}
impl<'a> Eq for ExprPtr<'a> {}

impl<'a> std::hash::Hash for ExprPtr<'a> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.bits.get()) }
}

impl<'a> std::fmt::Debug for ExprPtr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ExprPtr({:p}{})", self.as_ref(), if self.is_local() { ",L" } else { "" })
    }
}

const _: () = assert!(std::mem::align_of::<Expr<'static>>() >= 8);
const _: () = assert!(std::mem::size_of::<Option<ExprPtr<'static>>>() == 8);
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

const LEVELS_ADDR_MASK: u64 = 0x0000_ffff_ffff_ffff;
const LEVELS_TAG: u64 = 1 << 63;
const LEVELS_LEN_SHIFT: u32 = 48;
const LEVELS_LEN_MAX: usize = (1 << 15) - 1;

pub struct LevelsPtr<'a> {
    bits: std::num::NonZeroU64,
    _ph: PhantomData<&'a [LevelPtr<'a>]>,
}

impl<'a> LevelsPtr<'a> {
    #[inline]
    fn pack(s: &'a [LevelPtr<'a>], tag: u64) -> Self {
        let addr = s.as_ptr() as usize as u64;
        debug_assert!(addr & !LEVELS_ADDR_MASK == 0, "level slice address exceeds 48 bits");
        assert!(s.len() <= LEVELS_LEN_MAX, "universe parameter list too long");
        let bits = addr | ((s.len() as u64) << LEVELS_LEN_SHIFT) | tag | 1;
        Self { bits: unsafe { std::num::NonZeroU64::new_unchecked(bits) }, _ph: PhantomData }
    }

    #[inline]
    pub(crate) fn global(s: &'a [LevelPtr<'a>]) -> Self { Self::pack(s, 0) }

    #[inline]
    pub(crate) fn local(s: &'a [LevelPtr<'a>]) -> Self { Self::pack(s, LEVELS_TAG) }

    #[inline]
    #[allow(dead_code)]
    pub(crate) fn is_local(self) -> bool { self.bits.get() & LEVELS_TAG != 0 }

    #[inline]
    pub(crate) fn len(self) -> usize { ((self.bits.get() >> LEVELS_LEN_SHIFT) & 0x7fff) as usize }

    #[inline]
    pub(crate) fn as_ref(self) -> &'a [LevelPtr<'a>] {
        let p = (self.bits.get() & LEVELS_ADDR_MASK & !1) as usize as *const LevelPtr<'a>;
        unsafe { std::slice::from_raw_parts(p, self.len()) }
    }

    #[inline]
    #[allow(dead_code)]
    pub(crate) fn get_hash(&self) -> u64 { self.bits.get() }
}

impl<'a> Clone for LevelsPtr<'a> {
    #[inline]
    fn clone(&self) -> Self { *self }
}
impl<'a> Copy for LevelsPtr<'a> {}
unsafe impl<'a> Send for LevelsPtr<'a> {}
unsafe impl<'a> Sync for LevelsPtr<'a> {}

impl<'a> std::ops::Deref for LevelsPtr<'a> {
    type Target = [LevelPtr<'a>];
    #[inline]
    fn deref(&self) -> &[LevelPtr<'a>] { self.as_ref() }
}
impl<'a> PartialEq for LevelsPtr<'a> {
    #[inline]
    fn eq(&self, o: &Self) -> bool { self.bits == o.bits }
}
impl<'a> Eq for LevelsPtr<'a> {}
impl<'a> std::hash::Hash for LevelsPtr<'a> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.bits.get()) }
}
impl<'a> std::fmt::Debug for LevelsPtr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "LevelsPtr({:?})", self.as_ref()) }
}

macro_rules! interner {
    ($name:ident, $pointee:ident) => {
        pub(crate) struct $name<'a> {
            table: HashTable<&'a $pointee<'a>>,
        }
        impl<'a> $name<'a> {
            fn new() -> Self { Self { table: HashTable::new() } }
            #[allow(dead_code)]
            fn with_capacity(cap: usize) -> Self { Self { table: HashTable::with_capacity(cap) } }
            #[allow(dead_code)]
            pub(crate) fn len(&self) -> usize { self.table.len() }

            #[allow(dead_code)]
            pub(crate) fn clear(&mut self) { self.table.clear() }

            pub(crate) fn get<'b>(&self, v: &$pointee<'b>) -> Option<&'a $pointee<'a>>
            where
                'a: 'b, {
                let hash = v.raw_hash();
                self.table
                    .find(hash, |stored| {
                        let s: &$pointee<'b> = stored;
                        s == v
                    })
                    .copied()
            }

            pub(crate) fn insert(&mut self, arena: &ArenaRef<'a>, v: $pointee<'a>) -> &'a $pointee<'a> {
                let hash = v.raw_hash();
                let r: &'a $pointee<'a> = arena.alloc(v);
                self.table.insert_unique(hash, r, |s| s.raw_hash());
                r
            }

            #[allow(dead_code)]
            pub(crate) fn intern(&mut self, arena: &ArenaRef<'a>, v: $pointee<'a>) -> &'a $pointee<'a> {
                if let Some(r) = self.get(&v) {
                    return r
                }
                self.insert(arena, v)
            }
        }
    };
}

pub(crate) struct NameInterner<'a> {
    table: HashTable<&'a crate::name::NameNode<'a>>,
}
impl<'a> NameInterner<'a> {
    fn new() -> Self { Self { table: HashTable::new() } }

    fn with_capacity(cap: usize) -> Self { Self { table: HashTable::with_capacity(cap) } }

    pub(crate) fn get<'b>(&self, v: &Name<'b>) -> Option<&'a crate::name::NameNode<'a>>
    where
        'a: 'b, {
        let hash = v.get_hash();
        self.table.find(hash, |stored| stored.kind.get_hash() == hash && &stored.kind == unsafe { transmute_name(v) }).copied()
    }

    pub(crate) fn insert(&mut self, arena: &ArenaRef<'a>, v: Name<'a>) -> &'a crate::name::NameNode<'a> {
        let hash = v.get_hash();
        let r: &'a crate::name::NameNode<'a> = arena.alloc(crate::name::NameNode::new(v));
        self.table.insert_unique(hash, r, |s| s.kind.get_hash());
        r
    }

    pub(crate) fn intern(&mut self, arena: &ArenaRef<'a>, v: Name<'a>) -> &'a crate::name::NameNode<'a> {
        if let Some(r) = self.get(&v) {
            return r
        }
        self.insert(arena, v)
    }
}

#[inline]
unsafe fn transmute_name<'r, 'x, 'y>(n: &'r Name<'x>) -> &'r Name<'y> { unsafe { std::mem::transmute(n) } }

interner!(LevelInterner, Level);
interner!(ExprInterner, Expr);
interner!(StringInterner, CowStr);

impl<'a> ExprInterner<'a> {

}

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
            return r
        }
        self.insert(arena, v)
    }
}

pub(crate) struct LevelsInterner<'a> {
    table: HashTable<&'a [LevelPtr<'a>]>,
}
impl<'a> LevelsInterner<'a> {
    fn new() -> Self { Self { table: HashTable::new() } }
    fn with_capacity(cap: usize) -> Self { Self { table: HashTable::with_capacity(cap) } }
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
            return r
        }
        let hash = v.struct_hash();
        let r: &'a [LevelPtr<'a>] = arena.alloc_slice_copy(v);
        self.table.insert_unique(hash, r, |s| s.struct_hash());
        r
    }
}

pub struct Dag<'a> {
    pub(crate) names: NameInterner<'a>,
    pub(crate) levels: LevelInterner<'a>,
    pub(crate) exprs: ExprInterner<'a>,
    pub(crate) uparams: LevelsInterner<'a>,
    pub(crate) strings: StringInterner<'a>,
    pub(crate) bignums: Option<BigUintInterner<'a>>,
}

impl<'a> Dag<'a> {
    pub(crate) fn new(config: &Config, input_len: usize) -> Self {
        Self {
            names: NameInterner::with_capacity(input_len / 1024 + 16),
            levels: LevelInterner::new(),
            exprs: ExprInterner::new(),
            uparams: LevelsInterner::new(),
            strings: StringInterner::with_capacity(input_len / 16384 + 16),
            bignums: if config.nat_extension { Some(BigUintInterner::new()) } else { None },
        }
    }

    pub(crate) fn new_local(config: &Config) -> Self {
        Self {
            names: NameInterner::new(),
            levels: LevelInterner::with_capacity(14),
            exprs: ExprInterner::with_capacity(14),
            uparams: LevelsInterner::with_capacity(14),
            strings: StringInterner::new(),
            bignums: if config.nat_extension { Some(BigUintInterner::new()) } else { None },
        }
    }
}


pub(crate) fn new_fx_index_map<K, V>() -> FxIndexMap<K, V> { FxIndexMap::with_hasher(Default::default()) }

pub(crate) fn new_fx_hash_map<K, V>() -> FxHashMap<K, V> { FxHashMap::with_hasher(Default::default()) }

pub(crate) fn small_fx_hash_map<K, V>() -> FxHashMap<K, V> {
    FxHashMap::with_capacity_and_hasher(14, Default::default())
}

pub(crate) const SESSION_MAP_CAP: usize = 1 << 13;

pub(crate) const SESSION_MAP_CAP_SMALL: usize = 1 << 12;

pub(crate) fn session_small_fx_hash_map<K, V>() -> FxHashMap<K, V> {
    FxHashMap::with_capacity_and_hasher(SESSION_MAP_CAP_SMALL, Default::default())
}

pub(crate) fn session_small_fx_hash_set<K>() -> FxHashSet<K> {
    FxHashSet::with_capacity_and_hasher(SESSION_MAP_CAP_SMALL, Default::default())
}

pub(crate) fn session_fx_hash_map<K, V>() -> FxHashMap<K, V> {
    FxHashMap::with_capacity_and_hasher(SESSION_MAP_CAP, Default::default())
}

pub(crate) fn small_fx_hash_set<K>() -> FxHashSet<K> {
    FxHashSet::with_capacity_and_hasher(14, Default::default())
}


pub(crate) fn new_fx_hash_set<K>() -> FxHashSet<K> { FxHashSet::with_hasher(Default::default()) }


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

pub(crate) fn nat_sub(x: BigUint, y: BigUint) -> BigUint {
    if y > x {
        BigUint::zero()
    } else {
        x - y
    }
}

pub(crate) fn nat_div(x: BigUint, y: BigUint) -> BigUint {
    if y.is_zero() {
        BigUint::zero()
    } else {
        x / y
    }
}

pub(crate) fn nat_mod(x: BigUint, y: BigUint) -> BigUint {
    if y.is_zero() {
        x
    } else {
        x % y
    }
}

pub(crate) fn nat_gcd(x: &BigUint, y: &BigUint) -> BigUint {
    x.gcd(y)
}

pub(crate) fn nat_xor(x: &BigUint, y: &BigUint) -> BigUint {
    x ^ y
}

fn shift_amount(y: &BigUint) -> Option<u64> { u64::try_from(y).ok() }

pub(crate) fn nat_shl(x: BigUint, y: BigUint) -> BigUint {
    let sh = shift_amount(&y).expect("Nat.shiftLeft: shift does not fit in a machine word");
    x << sh
}

pub(crate) fn nat_shr(x: BigUint, y: BigUint) -> BigUint {
    match shift_amount(&y) {
        Some(sh) => x >> sh,
        None => BigUint::zero(),
    }
}

pub(crate) fn nat_land(x: BigUint, y: BigUint) -> BigUint {
    x & y
}
pub(crate) fn nat_lor(x: BigUint, y: BigUint) -> BigUint {
    x | y
}

pub struct ExprCache<'t> {
    pub(crate) inst_cache: FxHashMap<(ExprPtr<'t>, u16), ExprPtr<'t>>,
    pub(crate) subst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    pub(crate) dsubst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    pub(crate) simplify_cache: FxHashMap<LevelPtr<'t>, LevelPtr<'t>>,
}

impl<'t> ExprCache<'t> {
    pub(crate) fn shrink(&mut self) {
        shrink_map(&mut self.inst_cache);
        shrink_map(&mut self.subst_cache);
        shrink_map(&mut self.dsubst_cache);
        shrink_map(&mut self.simplify_cache);
    }
}

impl<'t> ExprCache<'t> {
    fn new() -> Self {
        Self {
            inst_cache: small_fx_hash_map(),
            subst_cache: small_fx_hash_map(),
            dsubst_cache: small_fx_hash_map(),
            simplify_cache: small_fx_hash_map(),
        }
    }
}

pub struct ExportFile<'p> {
    pub(crate) dag: Dag<'p>,
    pub(crate) anon: NamePtr<'p>,
    pub(crate) zero: LevelPtr<'p>,
    pub declars: DeclarMap<'p>,
    pub notations: NotationMap<'p>,
    pub name_cache: NameCache<'p>,
    pub config: Config,
    pub mutual_block_sizes: FxHashMap<NamePtr<'p>, (usize, usize)>,
}

impl<'p> ExportFile<'p> {
    pub fn new_env(&self, env_limit: EnvLimit<'p>) -> Env<'_, '_> { Env::new(&self.declars, &self.notations, env_limit) }

    pub fn with_ctx<F, A>(&self, f: F) -> A
    where
        F: for<'t> FnOnce(&mut TcCtx<'t, 'p>, &mut TcCache<'t, 't>, &'t bumpalo::Bump) -> A, {
        let mut arena = Arena::new();
        arena.with_scope(|scope| {
            let bump = bumpalo::Bump::new();
            let mut ctx = TcCtx::new(self, scope);
            let mut cache = TcCache::new(&bump);
            f(&mut ctx, &mut cache, &bump)
        })
    }

    pub fn with_tc<F, A>(&self, env_limit: EnvLimit<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        self.with_ctx(|ctx, cache, bump| {
            let env = ctx.export_file.new_env(env_limit);
            let mut tc = TypeChecker::new(ctx, &env, bump, None, cache);
            f(&mut tc)
        })
    }

    pub fn with_pp<F, A>(&self, f: F) -> A
    where
        F: FnOnce(&mut PrettyPrinter<'_, '_, 'p>) -> A, {
        self.with_ctx(|ctx, _cache, arena| ctx.with_pp(arena, f))
    }

}

pub struct TcCtx<'t, 'p> {
    pub(crate) export_file: &'t ExportFile<'p>,
    pub(crate) arena: &'t ArenaRef<'t>,
    pub(crate) dag: Dag<'t>,
    pub(crate) expr_cache: ExprCache<'t>,
    pub(crate) sig_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), crate::relevance::Sig>,
    pub(crate) sig_computing: FxHashSet<(NamePtr<'t>, LevelsPtr<'t>)>,
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub fn new(export_file: &'t ExportFile<'p>, arena: &'t ArenaRef<'t>) -> Self {
        let dag = Dag::new_local(&export_file.config);
        Self {
            export_file,
            arena,
            dag,
            expr_cache: ExprCache::new(),
            sig_cache: session_fx_hash_map(),
            sig_computing: small_fx_hash_set(),
        }
    }

    pub fn with_tc<F, A>(
        &mut self,
        env_limit: EnvLimit<'p>,
        arena: &'t bumpalo::Bump,
        cache: &mut TcCache<'t, 't>,
        f: F,
    ) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let env = self.export_file.new_env(env_limit);
        let mut tc = TypeChecker::new(self, &env, arena, None, cache);
        f(&mut tc)
    }

    pub fn with_tc_and_env_ext<'x, F, A>(
        &mut self,
        env_ext: &'x DeclarMap<'t>,
        env_limit: EnvLimit<'p>,
        arena: &'t bumpalo::Bump,
        cache: &mut TcCache<'t, 't>,
        f: F,
    ) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let env = Env::new_w_temp_ext(&self.export_file.declars, Some(env_ext), &self.export_file.notations, env_limit);
        let mut tc = TypeChecker::new(self, &env, arena, None, cache);
        f(&mut tc)
    }

    pub fn with_pp<F, A>(&mut self, arena: &'t bumpalo::Bump, f: F) -> A
    where
        F: FnOnce(&mut PrettyPrinter<'_, 't, 'p>) -> A, {
        f(&mut PrettyPrinter::new(self, arena))
    }

    pub fn read_name(&self, p: NamePtr<'t>) -> Name<'t> { p.as_ref().kind }

    pub fn read_name_pr(&self, p: NamePtr<'t>, q: NamePtr<'t>) -> (Name<'t>, Name<'t>) {
        (self.read_name(p), self.read_name(q))
    }

    pub fn read_level(&self, p: LevelPtr<'t>) -> Level<'t> { *p.as_ref() }

    pub fn read_level_pair(&self, a: LevelPtr<'t>, x: LevelPtr<'t>) -> (Level<'t>, Level<'t>) {
        (self.read_level(a), self.read_level(x))
    }

    pub fn read_expr(&self, p: ExprPtr<'t>) -> Expr<'t> { *p.as_ref() }

    #[inline]
    pub fn read_expr_ref(&self, p: ExprPtr<'t>) -> &Expr<'t> { p.as_ref() }

    pub fn read_string(&self, p: StringPtr<'t>) -> &CowStr<'t> { p.as_ref() }

    pub fn read_bignum(&self, p: BigUintPtr<'t>) -> Option<&BigUint> { Some(p.as_ref()) }

    pub fn read_levels(&self, p: LevelsPtr<'t>) -> &'t [LevelPtr<'t>] { p.as_ref() }

    pub fn alloc_name(&mut self, n: Name<'t>) -> NamePtr<'t> {
        if let Some(r) = self.export_file.dag.names.get(&n) {
            return NamePtr::global(r)
        }
        NamePtr::local(self.dag.names.intern(self.arena, n))
    }

    pub fn alloc_level(&mut self, l: Level<'t>) -> LevelPtr<'t> {
        if let Some(r) = self.export_file.dag.levels.get(&l) {
            return LevelPtr::global(r)
        }
        LevelPtr::local(self.dag.levels.intern(self.arena, l))
    }

    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        if let Some(r) = self.dag.exprs.get(&e) {
            return ExprPtr::local(r)
        }
        ExprPtr::local(self.dag.exprs.insert(self.arena, e))
    }

    pub(crate) fn alloc_string(&mut self, s: CowStr<'t>) -> StringPtr<'t> {
        if let Some(r) = self.export_file.dag.strings.get(&s) {
            return StringPtr::global(r)
        }
        StringPtr::local(self.dag.strings.intern(self.arena, s))
    }

    pub(crate) fn alloc_bignum(&mut self, n: BigUint) -> Option<BigUintPtr<'t>> {
        if let Some(global) = self.export_file.dag.bignums.as_ref() {
            if let Some(r) = global.get(&n) {
                return Some(BigUintPtr::global(r))
            }
        }
        let local = self.dag.bignums.as_mut()?;
        Some(BigUintPtr::local(local.intern(self.arena, n)))
    }

    pub fn alloc_levels(&mut self, ls: &[LevelPtr<'t>]) -> LevelsPtr<'t> {
        if let Some(r) = self.export_file.dag.uparams.get(ls) {
            return LevelsPtr::global(r)
        }
        LevelsPtr::local(self.dag.uparams.intern(self.arena, ls))
    }

    pub fn alloc_levels_slice(&mut self, ls: &[LevelPtr<'t>]) -> LevelsPtr<'t> { self.alloc_levels(ls) }

    pub fn anonymous(&self) -> NamePtr<'t> { self.export_file.anon }

    pub fn str(&mut self, pfx: NamePtr<'t>, sfx: StringPtr<'t>) -> NamePtr<'t> {
        let hash = hash64!(STR_HASH, pfx, sfx);
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
        let hash = hash64!(NUM_HASH, pfx, sfx);
        self.alloc_name(Name::Num(pfx, sfx, hash))
    }

    pub fn succ(&mut self, l: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(SUCC_HASH, l);
        self.alloc_level(Level::Succ(l, hash))
    }

    pub fn max(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(MAX_HASH, l, r);
        self.alloc_level(Level::Max(l, r, hash))
    }
    pub fn imax(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(IMAX_HASH, l, r);
        self.alloc_level(Level::IMax(l, r, hash))
    }
    pub fn param(&mut self, n: NamePtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(PARAM_HASH, n);
        self.alloc_level(Level::Param(n, hash))
    }

    pub fn mk_var(&mut self, dbj_idx: u16) -> ExprPtr<'t> {
        let hash = hash64!(VAR_HASH, dbj_idx);
        self.alloc_expr(Expr::Var { dbj_idx, hash })
    }

    pub fn mk_sort(&mut self, level: LevelPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(SORT_HASH, level);
        self.alloc_expr(Expr::Sort { level, hash })
    }

    pub fn mk_const(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(CONST_HASH, name, levels);
        self.alloc_expr(Expr::Const { name, levels, hash })
    }

    pub fn mk_app(&mut self, fun: ExprPtr<'t>, arg: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(APP_HASH, fun, arg);
        let fv_mask = crate::expr::child_mask(fun) | crate::expr::child_mask(arg);
        self.alloc_expr(Expr::App { fun, arg, fv_mask, hash })
    }

    pub fn mk_lambda(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let hash = hash64!(LAMBDA_HASH, binder_name, binder_style, binder_type, body);
        let fv_mask = crate::expr::child_mask(binder_type) | crate::expr::body_mask(body);
        self.alloc_expr(Expr::Lambda {
            binder_name,
            binder_style,
            binder_type,
            body,
            fv_mask,
            hash,
        })
    }

    pub fn mk_pi(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let hash = hash64!(PI_HASH, binder_name, binder_style, binder_type, body);
        let fv_mask = crate::expr::child_mask(binder_type) | crate::expr::body_mask(body);
        self.alloc_expr(Expr::Pi {
            binder_name,
            binder_style,
            binder_type,
            body,
            fv_mask,
            hash,
        })
    }

    pub fn mk_let(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        nondep: bool,
    ) -> ExprPtr<'t> {
        let hash = hash64!(LET_HASH, binder_name, binder_type, val, body, nondep);
        let fv_mask =
            crate::expr::child_mask(binder_type) | crate::expr::child_mask(val) | crate::expr::body_mask(body);
        let data = self.arena.alloc(crate::expr::LetData { binder_name, binder_type, val, body, nondep });
        self.alloc_expr(Expr::Let { data, fv_mask, hash })
    }

    pub fn mk_proj(&mut self, ty_name: NamePtr<'t>, idx: u16, structure: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(PROJ_HASH, ty_name, idx, structure);
        let fv_mask = crate::expr::child_mask(structure);
        self.alloc_expr(Expr::Proj { ty_name, idx, structure, fv_mask, hash })
    }

    pub fn mk_string_lit(&mut self, string_ptr: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.string_extension {
            return None;
        }
        let hash = hash64!(STRING_LIT_HASH, string_ptr);
        Some(self.alloc_expr(Expr::StringLit { ptr: string_ptr, hash }))
    }

    pub fn mk_string_lit_quick(&mut self, s: CowStr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.string_extension {
            return None;
        }
        let string_ptr = self.alloc_string(s);
        self.mk_string_lit(string_ptr)
    }

    pub fn mk_nat_lit(&mut self, num_ptr: BigUintPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.nat_extension {
            return None;
        }
        let hash = hash64!(NAT_LIT_HASH, num_ptr);
        Some(self.alloc_expr(Expr::NatLit { ptr: num_ptr, hash }))
    }

    pub fn mk_nat_lit_quick(&mut self, n: BigUint) -> Option<ExprPtr<'t>> {
        let num_ptr = self.alloc_bignum(n)?;
        self.mk_nat_lit(num_ptr)
    }





}

impl<'a> StringInterner<'a> {
    pub(crate) fn get_str(&self, s: &str) -> Option<&'a CowStr<'a>> {
        let hash = s.struct_hash();
        self.table.find(hash, |stored| stored.as_ref() == s).copied()
    }
}

impl<'a> Dag<'a> {
    fn get_string_ptr(&self, s: &str) -> Option<StringPtr<'a>> { self.strings.get_str(s).map(StringPtr::global) }

    fn find_name(&self, anon: NamePtr<'a>, dot_separated_name: &str) -> Option<NamePtr<'a>> {
        let mut pfx = anon;
        for s in dot_separated_name.split('.') {
            if let Ok(num) = s.parse::<u64>() {
                let hash = hash64!(NUM_HASH, pfx, num);
                if let Some(r) = self.names.get(&Name::Num(pfx, num, hash)) {
                    pfx = NamePtr::global(r);
                    continue;
                }
            } else if let Some(sfx) = self.get_string_ptr(s) {
                let hash = hash64!(STR_HASH, pfx, sfx);
                if let Some(r) = self.names.get(&Name::Str(pfx, sfx, hash)) {
                    pfx = NamePtr::global(r);
                    continue;
                }
            }
            return None;
        }
        Some(pfx)
    }

    pub(crate) fn mk_name_cache(&self, anon: NamePtr<'a>) -> NameCache<'a> {
        let cache = self.mk_name_cache_aux(anon);
        use crate::name::NatRed;
        let kinds = [
            (cache.nat_succ, NatRed::Succ),
            (cache.nat_div_go, NatRed::DivGo),
            (cache.nat_mod_core_go, NatRed::ModCoreGo),
            (cache.nat_add, NatRed::Add),
            (cache.nat_sub, NatRed::Sub),
            (cache.nat_mul, NatRed::Mul),
            (cache.nat_pow, NatRed::Pow),
            (cache.nat_mod, NatRed::Mod),
            (cache.nat_div, NatRed::Div),
            (cache.nat_beq, NatRed::Beq),
            (cache.nat_ble, NatRed::Ble),
            (cache.nat_land, NatRed::LAnd),
            (cache.nat_lor, NatRed::LOr),
            (cache.nat_xor, NatRed::XOr),
            (cache.nat_gcd, NatRed::Gcd),
            (cache.nat_shl, NatRed::Shl),
            (cache.nat_shr, NatRed::Shr),
        ];
        for (n, k) in kinds {
            if let Some(n) = n {
                n.as_ref().set_nat_red(k);
            }
        }
        cache
    }

    fn mk_name_cache_aux(&self, anon: NamePtr<'a>) -> NameCache<'a> {
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

pub(crate) const PRUNE_DM_LEN: usize = 1 << 10;
pub(crate) const PRUNE_DM_SHIFT: u32 = 64 - 10;

pub struct TcCache<'a, 't> {
    pub(crate) unfold_const_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) rec_rule_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) const_head_type_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) const_head_value_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) const_result_level_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), LevelPtr<'t>>,
    pub(crate) conv_uf: crate::union_find::UnionFind,
    pub(crate) conv_cache_neg: FxHashSet<(usize, usize)>,
    pub(crate) conv_cache_neg_probe: FxHashSet<(usize, usize)>,
    pub(crate) probe_depth: u32,
    pub(crate) closed_eval_cache: FxHashMap<ExprPtr<'t>, V<'a>>,
    pub(crate) whnf_store: FxHashMap<u64, (u128, ExprPtr<'t>)>,
    pub(crate) whnf_store_filter: Box<[u64; 1024]>,
    pub(crate) whnf_head_filter: Box<[u64; 1024]>,
    pub(crate) whnf_admit: Box<[u8; WHNF_ADMIT_LEN]>,
    pub(crate) lam_domain_cache: FxHashMap<usize, V<'a>>,
    pub(crate) global_value_cache: FxHashMap<(usize, u32), Result<(u128, bool), u8>>,
    pub(crate) open_eval_cache: FxHashMap<(usize, ExprPtr<'t>), V<'a>>,
    pub(crate) open_eval_seen: FxHashSet<ExprPtr<'t>>,
    pub(crate) bvar_hc: FxHashMap<(u32, usize), V<'a>>,
    pub(crate) spine_hc: FxHashMap<(usize, u64), S<'a>>,
    pub(crate) lam_hc: FxHashMap<(ExprPtr<'t>, usize, ExprPtr<'t>), V<'a>>,
    pub(crate) pi_hc: FxHashMap<(usize, usize, ExprPtr<'t>, usize), V<'a>>,
    pub(crate) type_cache: FxHashMap<(usize, ExprPtr<'t>), crate::infer::CachedType<'a>>,
    pub(crate) thunk_hc: FxHashMap<(usize, ExprPtr<'t>), V<'a>>,
    pub(crate) quote_cache: FxHashMap<(usize, u32), ExprPtr<'t>>,
    pub(crate) frames: hashbrown::HashTable<E<'a>>,
    pub(crate) lsub_bases: FxHashMap<usize, E<'a>>,
    pub(crate) level_subs: FxHashMap<(LevelsPtr<'t>, LevelsPtr<'t>), &'a crate::value::LevelSub<'a>>,
    pub(crate) prune_dm: Box<[(usize, u64, Option<E<'a>>); PRUNE_DM_LEN]>,
    pub(crate) rigid_hc: FxHashMap<(u8, u64, u64, usize), V<'a>>,
    pub(crate) unfold_hc: FxHashMap<(usize, usize), V<'a>>,
    pub(crate) iota_stuck: FxHashSet<usize>,
    pub(crate) struct_eta_cache: FxHashMap<(usize, NamePtr<'t>), Option<V<'a>>>,
    pub(crate) iota_cache: FxHashMap<usize, V<'a>>,
    pub(crate) canon_cache: FxHashMap<usize, V<'a>>,
    pub(crate) content_hc: FxHashMap<(u8, u64), V<'a>>,
    pub(crate) fvar_cache: FxHashMap<usize, bool>,
    pub(crate) ind_occ_cache: FxHashMap<usize, bool>,
    pub(crate) empty_env: E<'a>,
    pub(crate) empty_spine: S<'a>,
    pub(crate) empty_ctx: crate::value::C<'a>,
}

impl<'a, 't> TcCache<'a, 't> {
    pub(crate) fn new(arena: &'a bumpalo::Bump) -> Self {
        Self {
            unfold_const_cache: session_small_fx_hash_map(),
            rec_rule_cache: small_fx_hash_map(),
            const_head_type_cache: session_small_fx_hash_map(),
            const_head_value_cache: session_small_fx_hash_map(),
            const_result_level_cache: small_fx_hash_map(),
            conv_uf: crate::union_find::UnionFind::new(),
            conv_cache_neg: session_small_fx_hash_set(),
            conv_cache_neg_probe: small_fx_hash_set(),
            probe_depth: 0,
            closed_eval_cache: session_small_fx_hash_map(),
            whnf_store: new_fx_hash_map(),
            whnf_store_filter: Box::new([0u64; 1024]),
            whnf_head_filter: Box::new([0u64; 1024]),
            whnf_admit: vec![0u8; WHNF_ADMIT_LEN].into_boxed_slice().try_into().expect("admit table size"),
            lam_domain_cache: session_small_fx_hash_map(),
            global_value_cache: session_fx_hash_map(),
            open_eval_cache: session_fx_hash_map(),
            open_eval_seen: small_fx_hash_set(),
            bvar_hc: session_small_fx_hash_map(),
            spine_hc: session_fx_hash_map(),
            lam_hc: session_small_fx_hash_map(),
            pi_hc: session_small_fx_hash_map(),
            type_cache: session_fx_hash_map(),
            thunk_hc: session_fx_hash_map(),
            quote_cache: session_fx_hash_map(),
            frames: hashbrown::HashTable::with_capacity(SESSION_MAP_CAP),
            lsub_bases: small_fx_hash_map(),
            level_subs: small_fx_hash_map(),
            prune_dm: Box::new([(0, 0, None); PRUNE_DM_LEN]),
            rigid_hc: session_fx_hash_map(),
            unfold_hc: session_fx_hash_map(),
            iota_stuck: session_small_fx_hash_set(),
            struct_eta_cache: small_fx_hash_map(),
            iota_cache: session_fx_hash_map(),
            canon_cache: session_fx_hash_map(),
            content_hc: session_small_fx_hash_map(),
            fvar_cache: small_fx_hash_map(),
            ind_occ_cache: small_fx_hash_map(),
            empty_env: crate::value::env_empty(arena),
            empty_spine: crate::value::spine_empty(arena),
            empty_ctx: crate::value::ctx_empty(arena),
        }
    }

    pub(crate) fn clear(&mut self) {
        self.unfold_const_cache.clear();
        self.rec_rule_cache.clear();
        self.const_head_type_cache.clear();
        self.const_head_value_cache.clear();
        self.const_result_level_cache.clear();
        self.conv_uf.clear();
        self.conv_cache_neg.clear();
        self.conv_cache_neg_probe.clear();
        self.frames.clear();
        self.lsub_bases.clear();
        self.level_subs.clear();
        self.prune_dm.fill((0, 0, None));
        self.type_cache.clear();
        self.thunk_hc.clear();
        self.quote_cache.clear();
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
        self.ind_occ_cache.clear();
        self.closed_eval_cache.clear();
        self.lam_domain_cache.clear();
        self.global_value_cache.clear();
    }

    pub(crate) fn clear_session(&mut self) {
        self.probe_depth = 0;
        shrink_map(&mut self.unfold_const_cache);
        shrink_map(&mut self.rec_rule_cache);
        shrink_map(&mut self.const_head_type_cache);
        shrink_map(&mut self.const_head_value_cache);
        shrink_map(&mut self.const_result_level_cache);
        if self.conv_uf.capacity() > KEEP_CAP {
            self.conv_uf = crate::union_find::UnionFind::new();
        } else {
            self.conv_uf.clear();
        }
        shrink_set(&mut self.conv_cache_neg);
        shrink_set(&mut self.conv_cache_neg_probe);
        if self.frames.capacity() > KEEP_CAP {
            self.frames = hashbrown::HashTable::new();
        } else {
            self.frames.clear();
        }
        shrink_map(&mut self.lsub_bases);
        shrink_map(&mut self.level_subs);
        self.prune_dm.fill((0, 0, None));
        shrink_map(&mut self.type_cache);
        shrink_map(&mut self.thunk_hc);
        shrink_map(&mut self.quote_cache);
        shrink_map(&mut self.open_eval_cache);
        shrink_set(&mut self.open_eval_seen);
        shrink_map(&mut self.bvar_hc);
        shrink_map(&mut self.spine_hc);
        shrink_map(&mut self.lam_hc);
        shrink_map(&mut self.pi_hc);
        shrink_map(&mut self.rigid_hc);
        shrink_map(&mut self.unfold_hc);
        shrink_set(&mut self.iota_stuck);
        shrink_map(&mut self.struct_eta_cache);
        shrink_map(&mut self.iota_cache);
        shrink_map(&mut self.canon_cache);
        shrink_map(&mut self.content_hc);
        shrink_map(&mut self.fvar_cache);
        shrink_map(&mut self.ind_occ_cache);
        shrink_map(&mut self.closed_eval_cache);
        shrink_map(&mut self.lam_domain_cache);
        shrink_map(&mut self.global_value_cache);
    }
}

pub(crate) const KEEP_CAP: usize = 1 << 15;

fn shrink_map<K, V>(m: &mut FxHashMap<K, V>) {
    if m.capacity() > KEEP_CAP {
        *m = FxHashMap::default();
    } else {
        m.clear();
    }
}

fn shrink_set<K>(s: &mut FxHashSet<K>) {
    if s.capacity() > KEEP_CAP {
        *s = FxHashSet::default();
    } else {
        s.clear();
    }
}

pub(crate) struct SessionBump {
    inner: bumpalo::Bump,
}

impl SessionBump {
    pub(crate) fn new() -> Self { Self { inner: bumpalo::Bump::new() } }

    pub(crate) fn allocated_bytes(&self) -> usize { self.inner.allocated_bytes() }

    pub(crate) fn get<'a>(&self) -> &'a bumpalo::Bump {
        unsafe { &*(&self.inner as *const bumpalo::Bump) }
    }

    pub(crate) fn reset(&mut self) { self.inner = bumpalo::Bump::new() }
}

pub(crate) struct SessionCache<'b> {
    inner: TcCache<'b, 'b>,
}

impl<'b> SessionCache<'b> {
    pub(crate) fn new(base: &'b bumpalo::Bump) -> Self { Self { inner: TcCache::new(base) } }

    pub(crate) fn enter<'a, R>(&mut self, f: impl FnOnce(&mut TcCache<'a, 'a>) -> R) -> R {
        let p: *mut TcCache<'b, 'b> = &mut self.inner;
        let r = f(unsafe { &mut *(p as *mut TcCache<'a, 'a>) });
        self.inner.clear_session();
        r
    }
}


#[derive(Debug, Clone, Deserialize)]
pub struct Config {
    pub export_file_path: Option<PathBuf>,

    #[serde(default)]
    pub use_stdin: bool,

    pub permitted_axioms: Option<Vec<String>>,

    #[serde(default)]
    pub permit_standard_axioms: bool,

    #[serde(default = "default_true")]
    pub unpermitted_axiom_hard_error: bool,

    #[serde(default)]
    pub num_threads: usize,

    #[serde(default)]
    pub parse_only: bool,

    #[serde(default)]
    pub nat_extension: bool,
    #[serde(default)]
    pub string_extension: bool,

    pub pp_declars: Option<Vec<String>>,

    #[serde(default = "default_true")]
    pub unknown_pp_declar_hard_error: bool,

    #[serde(default)]
    pub pp_options: PpOptions,

    pub pp_output_path: Option<PathBuf>,

    #[serde(default)]
    pub pp_to_stdout: bool,

    #[serde(default)]
    pub print_success_message: bool,

    #[serde(default = "default_true")]
    pub print_axioms: bool,

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
                    return Err(Box::from(
                        "incompatible config options: must specify a path to an export file OR set `use_stdin: true`"
                            .to_string(),
                    ));
                }
                if config.export_file_path.is_some() && config.use_stdin {
                    return Err(Box::from(
                        "incompatible config options: if an export file path is given, `use_stdin` cannot be `true`"
                            .to_string(),
                    ));
                }
                if config.unsafe_permit_all_axioms {
                    if config.permit_standard_axioms {
                        return Err(Box::from(
                            "incompatible config options: unsafe_permit_all_axioms && permit_standard_axioms"
                                .to_string(),
                        ));
                    }
                    if config.unpermitted_axiom_hard_error {
                        return Err(Box::from(
                            "incompatible config options: unsafe_permit_all_axioms && unpermitted_axioms_hard_error"
                                .to_string(),
                        ));
                    }
                    if config.permitted_axioms.is_some() {
                        return Err(Box::from(
                            "incompatible config options: unsafe_permit_all_axioms && nonempty permitted_axioms list"
                                .to_string(),
                        ));
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

    pub fn to_export_file<'a>(self, arena: &'a ArenaRef<'a>) -> Result<(ExportFile<'a>, Vec<String>), Box<dyn Error>> {
        if let Some(pathbuf) = self.export_file_path.as_ref() {
            match OpenOptions::new().read(true).truncate(false).open(pathbuf) {
                Ok(file) => {
                    let map = unsafe { memmap2::Mmap::map(&file) }
                        .map_err(|e| -> Box<dyn Error> { Box::from(format!("Failed to map export file: {:?}", e)) })?;
                    parse_export_mapped(arena, &map, self)
                }
                Err(e) => Err(Box::from(format!("Failed to open export file: {:?}", e))),
            }
        } else if self.use_stdin {
            let reader = BufReader::new(std::io::stdin());
            parse_export_file(arena, reader, self)
        } else {
            panic!("Configuration file must specify en export file path or \"use_stdin\": true")
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct ExitStatus {
    tc_err: Option<String>,
    pp_err: Option<String>,
}

pub(crate) const WHNF_ADMIT_LEN: usize = 1 << 22;

#[inline]
pub(crate) fn admit_slot(k: u64) -> usize {
    (k.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 42) as usize
}

#[inline]
pub(crate) fn tenure_slot(k: usize) -> (usize, u64) {
    let h = (k as u64).wrapping_mul(0x9E3779B97F4A7C15) >> 16;
    (((h >> 6) as usize) & 1023, 1u64 << (h & 63))
}
