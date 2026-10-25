// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::infer::CachedType;
use crate::checker::ptrmap::{PtrMap, PtrSet};
use crate::checker::value::{E, LsubId, V, Vals};
use crate::term::hash::GOLDEN;
use crate::term::id::{ExprId, LevelId, LevelsId, NameId};

pub(crate) const PRUNE_DM_LEN: usize = 1 << 14;
pub(crate) const PRUNE_DM_SHIFT: u32 = 64 - 14;

pub(crate) const SESSION_BUDGET: usize = 9 * 1024 * 1024;
const ARENA_KEEP: usize = 4 * SESSION_BUDGET;

pub(crate) const SMALL: usize = 14;
pub(crate) const SESSION_SMALL: usize = 1 << 12;
pub(crate) const SESSION: usize = 1 << 13;

pub(crate) trait Reset {
    fn with_cap(cap: usize) -> Self;
    fn reset(&mut self);
    fn reset_shrink(&mut self);
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
    (@init $small:ident, cap($cap:expr)) => { Reset::with_cap(if $small { SMALL } else { $cap }) };
    (@init $small:ident, $kind:ident($init:expr)) => { $init };
    (@clear $f:expr, cap($cap:expr)) => { Reset::reset(&mut $f) };
    (@clear $f:expr, memos($init:expr)) => { $f.clear_memos() };
    (@clear $f:expr, $kind:ident($init:expr)) => {};
    (@clear_session $f:expr, cap($cap:expr)) => { Reset::reset_shrink(&mut $f) };
    (@clear_session $f:expr, keep($init:expr)) => {};
    (@clear_session $f:expr, session($init:expr)) => { $f = $init };
    (@clear_session $f:expr, memos($init:expr)) => { $f.reset(ARENA_KEEP) };
    (
        $vis:vis struct $name:ident {
            $(#[$kind:ident($arg:expr)] $f:ident: $t:ty,)*
        }
    ) => {
        $vis struct $name {
            $(pub(crate) $f: $t,)*
        }

        impl $name {
            pub(crate) fn new() -> Self {
                Self::with_size::<false>()
            }

            pub(crate) fn new_small() -> Self {
                Self::with_size::<true>()
            }

            fn with_size<const SMALL_MAPS: bool>() -> Self {
                Self {
                    $($f: caches!(@init SMALL_MAPS, $kind($arg)),)*
                }
            }

            pub(crate) fn clear(&mut self) {
                $(caches!(@clear self.$f, $kind($arg));)*
            }

            pub(crate) fn clear_session(&mut self) {
                $(caches!(@clear_session self.$f, $kind($arg));)*
            }
        }
    };
}

macro_rules! memo {
    ($map:expr, $key:expr, $compute:expr) => {{
        let key = $key;
        match $map.find(key) {
            Ok(v) => v,
            Err(at) => {
                let epoch = $map.epoch();
                let v = $compute;
                $map.insert_found(at, epoch, key, v);
                v
            }
        }
    }};
}
pub(crate) use memo;

caches! {
    pub struct TcCache {
        #[cap(SESSION_SMALL)] unfold_const_cache: PtrMap<(NameId, LevelsId), V>,
        #[cap(SMALL)] arithmetic_delta_cache: PtrMap<V, V>,
        #[cap(SMALL)] rec_rule_cache: PtrMap<(ExprId, LevelsId), V>,
        #[cap(SESSION_SMALL)] const_head_type_cache: PtrMap<(NameId, LevelsId), V>,
        #[cap(SESSION_SMALL)] const_head_value_cache: PtrMap<(NameId, LevelsId), V>,
        #[cap(SMALL)] const_result_level_cache: PtrMap<(NameId, LevelsId), LevelId>,
        #[cap(SESSION_SMALL)] conv_cache_pos: PtrSet<(V, V)>,
        #[cap(SESSION_SMALL)] conv_cache_neg: PtrSet<(V, V)>,
        #[cap(SMALL)] conv_cache_neg_probe: PtrSet<(V, V)>,
        #[session(0)] probe_depth: u32,
        #[session(0)] probe_budget: u32,
        #[session(false)] probe_exhausted: bool,
        #[session(None)] placeholder: Option<V>,
        #[cap(SESSION_SMALL)] closed_eval_cache: PtrMap<ExprId, V>,
        #[cap(SESSION_SMALL)] closed_lsub_eval_cache: PtrMap<(ExprId, LsubId), V>,
        #[keep(Reset::with_cap(SMALL))] whnf_store: PtrMap<u64, (u128, ExprId, ExprId)>,
        #[keep(Box::new([0; 1024]))] whnf_store_filter: Box<[u64; 1024]>,
        #[keep(Box::new([0; 1024]))] whnf_head_filter: Box<[u64; 1024]>,
        #[keep(vec![0; WHNF_ADMIT_LEN].into_boxed_slice().try_into().expect("admit table size"))]
        whnf_admit: Box<[u8; WHNF_ADMIT_LEN]>,
        #[cap(SESSION)] global_value_cache: PtrMap<(V, u32), Result<(u128, bool), u8>>,
        #[cap(SESSION)] open_eval_cache: PtrMap<(E, ExprId), V>,
        #[cap(SESSION)] type_cache: PtrMap<(E, ExprId), CachedType>,
        #[cap(SESSION)] quote_cache: PtrMap<(V, u32), ExprId>,
        #[cap(SMALL)] level_subs: PtrMap<(LevelsId, LevelsId), LsubId>,
        #[cap(0)] prune_dm: Box<[(u64, E, E); PRUNE_DM_LEN]>,
        #[cap(SMALL)] struct_eta_cache: PtrMap<(V, NameId), Option<V>>,
        #[cap(SMALL)] ind_occ_cache: PtrMap<V, bool>,
        #[memos(Vals::new())] vals: Vals,
    }
}

pub struct ExprCache {
    pub(crate) inst: PtrMap<(ExprId, u16), ExprId>,
    pub(crate) subst: PtrMap<(ExprId, LevelsId, LevelsId), ExprId>,
    pub(crate) dsubst: PtrMap<(ExprId, LevelsId, LevelsId), ExprId>,
    pub(crate) simplify: PtrMap<LevelId, LevelId>,
}

impl ExprCache {
    pub(crate) fn new() -> Self {
        ExprCache {
            inst: Reset::with_cap(SMALL),
            subst: Reset::with_cap(SMALL),
            dsubst: Reset::with_cap(SMALL),
            simplify: Reset::with_cap(SMALL),
        }
    }

    pub(crate) fn clear_session(&mut self) {
        self.inst.reset_shrink();
        self.subst.reset_shrink();
        self.dsubst.reset_shrink();
    }
}

pub(crate) const WHNF_ADMIT_LEN: usize = 1 << 22;

#[inline]
pub(crate) fn admit_slot(k: u64) -> usize {
    (k.wrapping_mul(GOLDEN) >> 42) as usize
}

#[inline]
pub(crate) fn tenure_slot(k: u64) -> (usize, u64) {
    let h = k.wrapping_mul(GOLDEN) >> 16;
    (((h >> 6) as usize) & 1023, 1u64 << (h & 63))
}
