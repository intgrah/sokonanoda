// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::memo;
use crate::checker::tc::TypeChecker;
use crate::checker::value::{C, Closure, DUMMY, E, EMPTY_ENV, Elim, FAR, LsubId, RigidHead, S, V};
use crate::outcome::reject;
use crate::term::hash::GOLDEN;
use crate::term::id::{BigId, ExprId, LevelId, LevelsId, NameId, StrId};
use std::mem::MaybeUninit;

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

    #[inline]
    pub(crate) fn prune_env(&mut self, e: E, mask: u64) -> E {
        if mask == 0 {
            let lsub = self.vals().env_lsub(e);
            return self.lsub_base(lsub);
        }
        let len = self.vals().env_len(e);
        if mask & FAR == 0 && len != 0 && len < 64 && mask == (1u64 << len) - 1 {
            return e;
        }
        let slot = prune_slot(e, mask);
        let ent = self.tc_cache.prune_dm[slot];
        if ent.0 == Some(e)
            && ent.1 == mask
            && let Some(hit) = ent.2
        {
            return hit;
        }
        self.prune_env_cold(e, mask, slot)
    }

    #[inline(never)]
    fn prune_env_cold(&mut self, e: E, mask: u64, first: usize) -> E {
        if mask == u64::MAX {
            return e;
        }
        let wide = mask & FAR != 0;
        let lsub = self.vals().env_lsub(e);
        let mut path: [MaybeUninit<(E, usize)>; 64] = [const { MaybeUninit::uninit() }; 64];
        let mut depth = 0;
        let mut cur = e;
        let mut m = mask;
        let mut slot = first;
        let mut base;
        loop {
            let Some((_, parent)) = self.vals().env_cons(cur) else {
                reject!("loose bound variable during evaluation")
            };
            path[depth].write((cur, slot));
            depth += 1;
            cur = parent;
            m = (m >> 1) | (m & FAR);
            if m == 0 {
                base = self.lsub_base(lsub);
                break;
            }
            if m == u64::MAX {
                base = cur;
                break;
            }
            slot = prune_slot(cur, m);
            let ent = self.tc_cache.prune_dm[slot];
            if ent.0 == Some(cur)
                && ent.1 == m
                && let Some(hit) = ent.2
            {
                base = hit;
                break;
            }
        }
        for i in (0..depth).rev() {
            let (env, s) = unsafe { path[i].assume_init() };
            let mi = if wide {
                (mask >> i) | !(u64::MAX >> (i + 1))
            } else {
                mask >> i
            };
            let v = if mi & 1 != 0 {
                self.vals()
                    .env_cons(env)
                    .map_or(DUMMY, |(v, _)| v)
            } else {
                DUMMY
            };
            base = self.env_extend(base, v);
            self.tc_cache.prune_dm[s] = (Some(env), mi, Some(base));
        }
        base
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
