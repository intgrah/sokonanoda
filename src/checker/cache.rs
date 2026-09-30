use crate::checker::infer::CachedType;
use crate::checker::value::{self, C, Ctx, E, Env, KeyTag, LevelSub, S, Spine, V, Value};
use crate::term::hash::{FxHashMap, FxHashSet, GOLDEN};
use crate::term::ptr::{ExprPtr, Id, LevelPtr, LevelsPtr, NamePtr};
use bumpalo::Bump;
use hashbrown::HashTable;
use std::cell::OnceCell;

pub(crate) const PRUNE_DM_LEN: usize = 1 << 10;
pub(crate) const PRUNE_DM_SHIFT: u32 = 64 - 10;

pub(crate) const SMALL: usize = 14;
pub(crate) const SESSION_SMALL: usize = 1 << 12;
pub(crate) const SESSION: usize = 1 << 13;
const KEEP_CAP: usize = 1 << 15;

pub(crate) trait Reset {
    fn with_cap(cap: usize) -> Self;
    fn reset(&mut self);
    fn reset_shrink(&mut self);
}

impl<K, V> Reset for FxHashMap<K, V> {
    fn with_cap(cap: usize) -> Self {
        FxHashMap::with_capacity_and_hasher(cap, Default::default())
    }
    fn reset(&mut self) {
        self.clear();
    }
    fn reset_shrink(&mut self) {
        if self.capacity() > KEEP_CAP {
            *self = FxHashMap::default();
        } else {
            self.clear();
        }
    }
}

impl<K> Reset for FxHashSet<K> {
    fn with_cap(cap: usize) -> Self {
        FxHashSet::with_capacity_and_hasher(cap, Default::default())
    }
    fn reset(&mut self) {
        self.clear();
    }
    fn reset_shrink(&mut self) {
        if self.capacity() > KEEP_CAP {
            *self = FxHashSet::default();
        } else {
            self.clear();
        }
    }
}

impl<T> Reset for HashTable<T> {
    fn with_cap(cap: usize) -> Self {
        HashTable::with_capacity(cap)
    }
    fn reset(&mut self) {
        self.clear();
    }
    fn reset_shrink(&mut self) {
        if self.capacity() > KEEP_CAP {
            *self = HashTable::new();
        } else {
            self.clear();
        }
    }
}

impl<T: Copy + Default, const N: usize> Reset for Box<[T; N]> {
    fn with_cap(_: usize) -> Self {
        Box::new([T::default(); N])
    }
    fn reset(&mut self) {
        self.fill(T::default());
    }
    fn reset_shrink(&mut self) {
        self.reset();
    }
}

macro_rules! caches {
    (@init cap($cap:expr)) => { $crate::checker::cache::Reset::with_cap($cap) };
    (@init keep($init:expr)) => { $init };
    (@init session($init:expr)) => { $init };
    (@clear $f:expr, cap($cap:expr)) => { $crate::checker::cache::Reset::reset(&mut $f) };
    (@clear $f:expr, keep($init:expr)) => {};
    (@clear $f:expr, session($init:expr)) => {};
    (@clear_session $f:expr, cap($cap:expr)) => { $crate::checker::cache::Reset::reset_shrink(&mut $f) };
    (@clear_session $f:expr, keep($init:expr)) => {};
    (@clear_session $f:expr, session($init:expr)) => { $f = $init };
    (
        $vis:vis struct $name:ident<$($lt:lifetime),*> {
            $(#[$kind:ident($arg:expr)] $f:ident: $t:ty,)*
        }
        fn new($($param:ident: $pty:ty),*);
    ) => {
        $vis struct $name<$($lt),*> {
            $(pub(crate) $f: $t,)*
        }

        impl<$($lt),*> $name<$($lt),*> {
            pub(crate) fn new($($param: $pty),*) -> Self {
                Self {
                    $($f: caches!(@init $kind($arg)),)*
                }
            }

            #[allow(dead_code)]
            pub(crate) fn clear(&mut self) {
                $(caches!(@clear self.$f, $kind($arg));)*
            }

            pub(crate) fn clear_session(&mut self) {
                $(caches!(@clear_session self.$f, $kind($arg));)*
            }
        }
    };
}
pub(crate) use caches;

macro_rules! memo {
    ($map:expr, $key:expr, $compute:expr) => {{
        let key = $key;
        match $map.get(&key) {
            Some(&v) => v,
            None => {
                let v = $compute;
                $map.insert(key, v);
                v
            }
        }
    }};
}
pub(crate) use memo;

macro_rules! hashcons {
    ($map:expr, $key:expr, $make:expr) => {
        match $map.entry($key) {
            std::collections::hash_map::Entry::Occupied(o) => *o.get(),
            std::collections::hash_map::Entry::Vacant(slot) => *slot.insert($make),
        }
    };
}
pub(crate) use hashcons;

caches! {
    pub struct TcCache<'a, 't> {
        #[cap(SESSION_SMALL)] unfold_const_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
        #[cap(SMALL)] rec_rule_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>), V<'a>>,
        #[cap(SESSION_SMALL)] const_head_type_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
        #[cap(SESSION_SMALL)] const_head_value_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
        #[cap(SMALL)] const_result_level_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), LevelPtr<'t>>,
        #[cap(SESSION_SMALL)] conv_cache_pos: FxHashSet<(Id<'a, Value<'a>>, Id<'a, Value<'a>>)>,
        #[cap(SESSION_SMALL)] conv_cache_neg: FxHashSet<(Id<'a, Value<'a>>, Id<'a, Value<'a>>)>,
        #[cap(SMALL)] conv_cache_neg_probe: FxHashSet<(Id<'a, Value<'a>>, Id<'a, Value<'a>>)>,
        #[session(0)] probe_depth: u32,
        #[session(0)] probe_budget: u32,
        #[session(false)] probe_exhausted: bool,
        #[cap(SESSION_SMALL)] closed_eval_cache: FxHashMap<ExprPtr<'t>, V<'a>>,
        #[keep(FxHashMap::default())] whnf_store: FxHashMap<u64, (u128, ExprPtr<'t>)>,
        #[keep(Box::new([0; 1024]))] whnf_store_filter: Box<[u64; 1024]>,
        #[keep(Box::new([0; 1024]))] whnf_head_filter: Box<[u64; 1024]>,
        #[keep(vec![0; WHNF_ADMIT_LEN].into_boxed_slice().try_into().expect("admit table size"))]
        whnf_admit: Box<[u8; WHNF_ADMIT_LEN]>,
        #[cap(SESSION_SMALL)] lam_domain_cache: FxHashMap<Id<'a, Value<'a>>, V<'a>>,
        #[cap(SESSION)] global_value_cache: FxHashMap<(Id<'a, Value<'a>>, u32), Result<(u128, bool), u8>>,
        #[cap(SESSION)] open_eval_cache: FxHashMap<(Id<'a, Env<'a>>, ExprPtr<'t>), V<'a>>,
        #[cap(SESSION_SMALL)] bvar_hc: FxHashMap<(u32, Id<'a, Value<'a>>), V<'a>>,
        #[cap(SESSION)] spine_hc: FxHashMap<(Id<'a, Spine<'a>>, u64), S<'a>>,
        #[cap(SESSION)] app_hc: FxHashMap<(Id<'a, Value<'a>>, Id<'a, Value<'a>>), V<'a>>,
        #[cap(SESSION)] env_hc: FxHashMap<(Id<'a, Env<'a>>, Id<'a, Value<'a>>), E<'a>>,
        #[cap(SESSION_SMALL)] lam_hc: FxHashMap<(ExprPtr<'t>, Id<'a, Env<'a>>, ExprPtr<'t>), V<'a>>,
        #[cap(SESSION_SMALL)]
        pi_hc: FxHashMap<(Id<'a, Value<'a>>, Id<'a, Env<'a>>, ExprPtr<'t>, Option<Id<'a, Ctx<'a>>>), V<'a>>,
        #[cap(SESSION)] type_cache: FxHashMap<(Id<'a, Env<'a>>, ExprPtr<'t>), CachedType<'a>>,
        #[cap(SESSION)] quote_cache: FxHashMap<(Id<'a, Value<'a>>, u32), ExprPtr<'t>>,
        #[cap(SESSION)] frames: HashTable<E<'a>>,
        #[cap(SMALL)] lsub_bases: FxHashMap<Id<'a, LevelSub<'a>>, E<'a>>,
        #[cap(SMALL)] level_subs: FxHashMap<(LevelsPtr<'t>, LevelsPtr<'t>), &'a LevelSub<'a>>,
        #[cap(0)] prune_dm: Box<[(Option<Id<'a, Env<'a>>>, u64, Option<E<'a>>); PRUNE_DM_LEN]>,
        #[cap(SMALL)] wide_fvars: FxHashMap<ExprPtr<'t>, &'a [u16]>,
        #[cap(SMALL)] wide_prune: FxHashMap<(Id<'a, Env<'a>>, ExprPtr<'t>), E<'a>>,
        #[cap(SESSION)] rigid_hc: FxHashMap<(KeyTag, u64, u64, Id<'a, Spine<'a>>), V<'a>>,
        #[cap(SESSION)] unfold_hc: FxHashMap<(Id<'a, OnceCell<V<'a>>>, Id<'a, Spine<'a>>), V<'a>>,
        #[cap(SESSION_SMALL)] iota_stuck: FxHashSet<Id<'a, Value<'a>>>,
        #[cap(SMALL)] struct_eta_cache: FxHashMap<(Id<'a, Value<'a>>, NamePtr<'t>), Option<V<'a>>>,
        #[cap(SESSION)] iota_cache: FxHashMap<Id<'a, Value<'a>>, V<'a>>,
        #[cap(SESSION)] canon_cache: FxHashMap<Id<'a, Value<'a>>, V<'a>>,
        #[cap(SESSION_SMALL)] content_hc: FxHashMap<(KeyTag, u64), V<'a>>,
        #[cap(SMALL)] fvar_cache: FxHashMap<Id<'a, Value<'a>>, bool>,
        #[cap(SMALL)] ind_occ_cache: FxHashMap<Id<'a, Value<'a>>, bool>,
        #[keep(value::env_empty(arena))] empty_env: E<'a>,
        #[keep(value::spine_empty(arena))] empty_spine: S<'a>,
        #[keep(value::ctx_empty(arena))] empty_ctx: C<'a>,
    }
    fn new(arena: &'a Bump);
}

pub(crate) struct SessionBump {
    inner: bumpalo::Bump,
}

impl SessionBump {
    pub(crate) fn new() -> Self {
        Self {
            inner: bumpalo::Bump::new(),
        }
    }

    pub(crate) fn allocated_bytes(&self) -> usize {
        self.inner.allocated_bytes()
    }

    pub(crate) unsafe fn get<'a>(&self) -> &'a bumpalo::Bump {
        unsafe { &*(&self.inner as *const bumpalo::Bump) }
    }

    pub(crate) fn reset(&mut self) {
        self.inner = bumpalo::Bump::new()
    }
}

pub(crate) struct SessionCache<'b> {
    inner: TcCache<'b, 'b>,
}

impl<'b> SessionCache<'b> {
    pub(crate) fn new(base: &'b bumpalo::Bump) -> Self {
        Self {
            inner: TcCache::new(base),
        }
    }

    pub(crate) unsafe fn enter<'a>(
        &mut self,
        f: impl FnOnce(&mut TcCache<'a, 'a>) -> bool,
    ) -> bool {
        let p: *mut TcCache<'b, 'b> = &mut self.inner;
        let r = f(unsafe { &mut *(p as *mut TcCache<'a, 'a>) });
        self.inner.clear_session();
        r
    }
}

pub(crate) const WHNF_ADMIT_LEN: usize = 1 << 22;

#[inline]
pub(crate) fn admit_slot(k: u64) -> usize {
    (k.wrapping_mul(GOLDEN) >> 42) as usize
}

#[inline]
pub(crate) fn tenure_slot(k: usize) -> (usize, u64) {
    let h = (k as u64).wrapping_mul(GOLDEN) >> 16;
    (((h >> 6) as usize) & 1023, 1u64 << (h & 63))
}
