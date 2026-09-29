use crate::checker::value::{E, S, V};
use crate::term::hash::{
    new_fx_hash_map, session_fx_hash_map, session_small_fx_hash_map, session_small_fx_hash_set,
    small_fx_hash_map, small_fx_hash_set, FxHashMap, FxHashSet, SESSION_MAP_CAP,
};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};

pub(crate) const PRUNE_DM_LEN: usize = 1 << 10;
pub(crate) const PRUNE_DM_SHIFT: u32 = 64 - 10;

pub struct TcCache<'a, 't> {
    pub(crate) unfold_const_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) rec_rule_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) const_head_type_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) const_head_value_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), V<'a>>,
    pub(crate) const_result_level_cache: FxHashMap<(NamePtr<'t>, LevelsPtr<'t>), LevelPtr<'t>>,
    pub(crate) conv_cache_pos: FxHashSet<(usize, usize)>,
    pub(crate) conv_cache_neg: FxHashSet<(usize, usize)>,
    pub(crate) conv_cache_neg_probe: FxHashSet<(usize, usize)>,
    pub(crate) probe_depth: u32,
    pub(crate) probe_budget: u32,
    pub(crate) probe_exhausted: bool,
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
    pub(crate) app_hc: FxHashMap<(usize, usize), V<'a>>,
    pub(crate) env_hc: FxHashMap<(usize, usize), E<'a>>,
    pub(crate) lam_hc: FxHashMap<(ExprPtr<'t>, usize, ExprPtr<'t>), V<'a>>,
    pub(crate) pi_hc: FxHashMap<(usize, usize, ExprPtr<'t>, usize), V<'a>>,
    pub(crate) type_cache: FxHashMap<(usize, ExprPtr<'t>), crate::checker::infer::CachedType<'a>>,
    pub(crate) thunk_hc: FxHashMap<(usize, ExprPtr<'t>), V<'a>>,
    pub(crate) quote_cache: FxHashMap<(usize, u32), ExprPtr<'t>>,
    pub(crate) frames: hashbrown::HashTable<E<'a>>,
    pub(crate) lsub_bases: FxHashMap<usize, E<'a>>,
    pub(crate) level_subs:
        FxHashMap<(LevelsPtr<'t>, LevelsPtr<'t>), &'a crate::checker::value::LevelSub<'a>>,
    pub(crate) prune_dm: Box<[(usize, u64, Option<E<'a>>); PRUNE_DM_LEN]>,
    pub(crate) wide_fvars: FxHashMap<ExprPtr<'t>, &'a [u16]>,
    pub(crate) wide_prune: FxHashMap<(usize, ExprPtr<'t>), E<'a>>,
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
    pub(crate) empty_ctx: crate::checker::value::C<'a>,
}

impl<'a, 't> TcCache<'a, 't> {
    pub(crate) fn new(arena: &'a bumpalo::Bump) -> Self {
        Self {
            unfold_const_cache: session_small_fx_hash_map(),
            rec_rule_cache: small_fx_hash_map(),
            const_head_type_cache: session_small_fx_hash_map(),
            const_head_value_cache: session_small_fx_hash_map(),
            const_result_level_cache: small_fx_hash_map(),
            conv_cache_pos: session_small_fx_hash_set(),
            conv_cache_neg: session_small_fx_hash_set(),
            conv_cache_neg_probe: small_fx_hash_set(),
            probe_depth: 0,
            probe_budget: 0,
            probe_exhausted: false,
            closed_eval_cache: session_small_fx_hash_map(),
            whnf_store: new_fx_hash_map(),
            whnf_store_filter: Box::new([0u64; 1024]),
            whnf_head_filter: Box::new([0u64; 1024]),
            whnf_admit: vec![0u8; WHNF_ADMIT_LEN]
                .into_boxed_slice()
                .try_into()
                .expect("admit table size"),
            lam_domain_cache: session_small_fx_hash_map(),
            global_value_cache: session_fx_hash_map(),
            open_eval_cache: session_fx_hash_map(),
            open_eval_seen: small_fx_hash_set(),
            bvar_hc: session_small_fx_hash_map(),
            spine_hc: session_fx_hash_map(),
            app_hc: session_fx_hash_map(),
            env_hc: session_fx_hash_map(),
            lam_hc: session_small_fx_hash_map(),
            pi_hc: session_small_fx_hash_map(),
            type_cache: session_fx_hash_map(),
            thunk_hc: session_fx_hash_map(),
            quote_cache: session_fx_hash_map(),
            frames: hashbrown::HashTable::with_capacity(SESSION_MAP_CAP),
            lsub_bases: small_fx_hash_map(),
            level_subs: small_fx_hash_map(),
            prune_dm: Box::new([(0, 0, None); PRUNE_DM_LEN]),
            wide_fvars: small_fx_hash_map(),
            wide_prune: small_fx_hash_map(),
            rigid_hc: session_fx_hash_map(),
            unfold_hc: session_fx_hash_map(),
            iota_stuck: session_small_fx_hash_set(),
            struct_eta_cache: small_fx_hash_map(),
            iota_cache: session_fx_hash_map(),
            canon_cache: session_fx_hash_map(),
            content_hc: session_small_fx_hash_map(),
            fvar_cache: small_fx_hash_map(),
            ind_occ_cache: small_fx_hash_map(),
            empty_env: crate::checker::value::env_empty(arena),
            empty_spine: crate::checker::value::spine_empty(arena),
            empty_ctx: crate::checker::value::ctx_empty(arena),
        }
    }

    pub(crate) fn clear(&mut self) {
        self.unfold_const_cache.clear();
        self.rec_rule_cache.clear();
        self.const_head_type_cache.clear();
        self.const_head_value_cache.clear();
        self.const_result_level_cache.clear();
        self.conv_cache_pos.clear();
        self.conv_cache_neg.clear();
        self.conv_cache_neg_probe.clear();
        self.frames.clear();
        self.lsub_bases.clear();
        self.level_subs.clear();
        self.prune_dm.fill((0, 0, None));
        self.wide_fvars.clear();
        self.wide_prune.clear();
        self.type_cache.clear();
        self.thunk_hc.clear();
        self.quote_cache.clear();
        self.open_eval_cache.clear();
        self.open_eval_seen.clear();
        self.bvar_hc.clear();
        self.spine_hc.clear();
        self.app_hc.clear();
        self.env_hc.clear();
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
        self.probe_budget = 0;
        self.probe_exhausted = false;
        shrink_map(&mut self.unfold_const_cache);
        shrink_map(&mut self.rec_rule_cache);
        shrink_map(&mut self.const_head_type_cache);
        shrink_map(&mut self.const_head_value_cache);
        shrink_map(&mut self.const_result_level_cache);
        shrink_set(&mut self.conv_cache_pos);
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
        shrink_map(&mut self.wide_fvars);
        shrink_map(&mut self.wide_prune);
        shrink_map(&mut self.type_cache);
        shrink_map(&mut self.thunk_hc);
        shrink_map(&mut self.quote_cache);
        shrink_map(&mut self.open_eval_cache);
        shrink_set(&mut self.open_eval_seen);
        shrink_map(&mut self.bvar_hc);
        shrink_map(&mut self.spine_hc);
        shrink_map(&mut self.app_hc);
        shrink_map(&mut self.env_hc);
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

pub(super) fn shrink_map<K, V>(m: &mut FxHashMap<K, V>) {
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
    (k.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 42) as usize
}

#[inline]
pub(crate) fn tenure_slot(k: usize) -> (usize, u64) {
    let h = (k as u64).wrapping_mul(0x9E3779B97F4A7C15) >> 16;
    (((h >> 6) as usize) & 1023, 1u64 << (h & 63))
}
