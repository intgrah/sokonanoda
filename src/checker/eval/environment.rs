// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::memo;
use crate::checker::tc::TypeChecker;
use crate::checker::value::{C, Closure, E, EMPTY_ENV, Elim, EnvView, FAR, LsubId, NEAR, RigidHead, S, V};
use crate::term::hash::GOLDEN;
use crate::term::id::{BigId, ExprId, LevelId, LevelsId, NameId, StrId};

impl TypeChecker<'_, '_> {
    #[inline]
    pub(crate) fn mk_bvar_hc(&mut self, level: u32, ty: V) -> V {
        self.tc_cache.vals.mk_head(RigidHead::BVar(level, ty), false)
    }

    pub(crate) fn mk_sort_hc(&mut self, level: LevelId) -> V {
        self.tc_cache.vals.mk_sort(level)
    }

    pub(crate) fn mk_natlit_hc(&mut self, lit: BigId) -> V {
        self.tc_cache.vals.mk_natlit(lit)
    }

    pub(crate) fn mk_strlit_hc(&mut self, lit: StrId) -> V {
        self.tc_cache.vals.mk_strlit(lit)
    }

    pub(crate) fn mk_head_hc(&mut self, head: RigidHead) -> V {
        let active = self.nat_extension
            && matches!(head, RigidHead::Ctor(name, _) if Some(name) == self.ctx.export_file.name_cache.nat_succ);
        self.tc_cache.vals.mk_head(head, active)
    }

    pub(crate) fn mk_unfold_head(&mut self, name: NameId, levels: LevelsId) -> V {
        let active = self.nat_extension && self.ctx.export_file.nat_red(name).is_some();
        self.tc_cache.vals.mk_unfold_head(name, levels, active)
    }

    #[inline(always)]
    pub(crate) fn env_extend(&mut self, parent: E, v: V) -> E {
        self.tc_cache.vals.env_push(parent, v)
    }

    pub(crate) fn ctx_extend(&mut self, parent: C, ty: V) -> C {
        self.tc_cache.vals.ctx_extend(parent, ty)
    }

    pub(super) fn lsub_base(&mut self, lsub: Option<LsubId>) -> E {
        self.tc_cache.vals.env_nil(lsub)
    }

    fn intern_level_sub(&mut self, ks: LevelsId, vs: LevelsId) -> LsubId {
        memo!(
            self.tc_cache.level_subs,
            (ks, vs),
            self.tc_cache.vals.new_lsub(ks, vs)
        )
    }

    pub(crate) fn eval_inst(&mut self, ex: ExprId, ks: LevelsId, vs: LevelsId) -> V {
        debug_assert_eq!(self.ctx.levels(ks).len(), self.ctx.levels(vs).len());
        if ks == vs || self.ctx.levels(ks).is_empty() {
            return self.eval(0, EMPTY_ENV, ex);
        }
        let ls = self.intern_level_sub(ks, vs);
        let base = self.lsub_base(Some(ls));
        self.eval(0, base, ex)
    }

    #[inline(always)]
    pub(crate) fn prune_env(&mut self, e: E, mask: u64) -> E {
        if mask == 0 {
            let lsub = self.vals().env_lsub(e);
            return self.lsub_base(lsub);
        }
        if self.vals().env_is_pruned(e, mask) {
            return e;
        }
        let slot = prune_slot(e, mask);
        let (m, k, hit) = self.tc_cache.prune_dm[slot];
        if k == e && m == mask {
            return hit;
        }
        self.prune_env_cold(e, mask, slot)
    }

    fn frame_without(&mut self, dropped: u32, mask: u64, start: usize, cut: u32, rest: Option<E>, lsub: Option<LsubId>) -> Option<E> {
        let near = (mask & !FAR) >> dropped;
        if near == 0 && rest.is_none() {
            return None;
        }
        let skipped = (mask & ((1u64 << dropped) - 1)).count_ones() as usize;
        let kept = start + skipped;
        let vals = self.vals();
        let slots_hash = (kept..kept + near.count_ones() as usize).fold(lsub.map_or(0, |l| u64::from(l.raw())), |h, i| {
            h.wrapping_mul(GOLDEN).wrapping_add(u64::from(vals.env_slot(i).raw()))
        });
        Some(self.tc_cache.vals.intern_frame(slots_hash, near, kept, cut - dropped, rest, lsub).0)
    }

    #[inline(never)]
    fn prune_env_cold(&mut self, e: E, mask: u64, slot: usize) -> E {
        let lsub = self.vals().env_lsub(e);
        let start = self.vals().env_slots_end();
        let mut slots_hash = lsub.map_or(0, |l| u64::from(l.raw()));
        let mut out_mask = 0u64;
        let keep_far = mask & FAR != 0;
        let mut rem = mask & !FAR;
        let mut consumed = 0u32;
        let mut cur = e;
        let mut rest = None;
        loop {
            if consumed == NEAR {
                if keep_far {
                    rest = match self.vals().env_view(cur) {
                        EnvView::Nil | EnvView::Framed { mask: 0, .. } => None,
                        _ => Some(cur),
                    };
                }
                break;
            }
            if rem == 0 && !keep_far {
                break;
            }
            match self.vals().env_view(cur) {
                EnvView::Nil => break,
                EnvView::Framed {
                    mask: fmask,
                    start: fstart,
                    cut,
                    rest: frest,
                } => {
                    let taken = cut.min(NEAR - consumed);
                    let m2 = rem & fmask & ((1u64 << taken) - 1);
                    out_mask |= m2 << consumed;
                    let mut sel = m2;
                    while sel != 0 {
                        let below = fmask & ((1u64 << sel.trailing_zeros()) - 1);
                        sel &= sel - 1;
                        let sv = self.vals().env_slot(fstart + below.count_ones() as usize);
                        self.vals_mut().push_env_slot(sv);
                        slots_hash = slots_hash.wrapping_mul(GOLDEN).wrapping_add(u64::from(sv.raw()));
                    }
                    if taken < cut {
                        if keep_far {
                            rest = self.frame_without(taken, fmask, fstart, cut, frest, lsub);
                        }
                        break;
                    }
                    let Some(next) = frest else {
                        break;
                    };
                    rem >>= taken;
                    consumed += taken;
                    cur = next;
                }
                EnvView::Cons { v, parent } => {
                    if rem & 1 != 0 {
                        self.vals_mut().push_env_slot(v);
                        slots_hash = slots_hash.wrapping_mul(GOLDEN).wrapping_add(u64::from(v.raw()));
                        out_mask |= 1u64 << consumed;
                        rem >>= 1;
                        consumed += 1;
                        cur = parent;
                        continue;
                    }
                    let unrequested = rem.trailing_zeros().min(NEAR - consumed);
                    let mut hops = 0;
                    while hops < unrequested
                        && let Some((_, parent)) = self.vals().env_cons(cur)
                    {
                        cur = parent;
                        hops += 1;
                    }
                    rem >>= hops;
                    consumed += hops;
                }
            }
        }
        let (r, fresh) = self.tc_cache.vals.intern_frame(slots_hash, out_mask, start, NEAR, rest, lsub);
        if !fresh {
            self.vals_mut().drop_env_slots(start);
        }
        self.tc_cache.prune_dm[slot] = (mask, e, r);
        r
    }

    #[inline(always)]
    pub(crate) fn key_env(&mut self, env: E, e: ExprId) -> E {
        let mask = self.ctx.mask(e);
        self.prune_env(env, mask)
    }

    #[inline]
    pub(super) fn spine_snoc_hc(&mut self, prev: S, elim: Elim) -> S {
        self.tc_cache.vals.snoc(prev, elim)
    }

    #[inline]
    pub(crate) fn mk_lam_hc(&mut self, binder_type: ExprId, body: Closure) -> V {
        self.tc_cache.vals.mk_lam(binder_type, body)
    }

    #[inline]
    pub(crate) fn mk_pi_hc(&mut self, domain: V, body: Closure) -> V {
        self.tc_cache.vals.mk_pi(domain, body)
    }
}

#[inline]
fn prune_slot(env: E, mask: u64) -> usize {
    ((u64::from(env.raw()).wrapping_mul(GOLDEN) ^ mask.wrapping_mul(0xD6E8_FEB8_6659_FD93))
        >> crate::checker::cache::PRUNE_DM_SHIFT) as usize
}
