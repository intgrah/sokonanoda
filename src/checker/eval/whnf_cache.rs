// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::memo;
use crate::checker::tc::TypeChecker;
use crate::checker::value::{
    Closure, E, EMPTY_ENV, ElimView, KeyTag, RigidHead, S, V, Value, kmix,
};
use crate::term::id::{LevelsId, NameId};

#[inline]
fn mix(a: u128, b: u128) -> u128 {
    (a ^ b)
        .wrapping_mul(0x9E37_79B9_7F4A_7C15_BF58_476D_1CE4_E5B9)
        .rotate_left(47)
}

fn head_key(tag: KeyTag, n: NameId, ls: LevelsId) -> u128 {
    mix(mix(tag.u128(), u128::from(n.raw())), u128::from(ls.raw()))
}

const WHNF_ADMIT_THRESHOLD: u8 = 2;

const FAIL_CLOSURE: u8 = 1;
const FAIL_DEPTH: u8 = 7;

impl TypeChecker<'_, '_> {
    #[inline]
    pub(super) fn note_whnf(&mut self, depth: u32, src: V, res: V, steps: u32) {
        if steps == 0 {
            return;
        }
        let closed = self.vals_mut().is_closed(src);
        let k = self.vals_mut().digest(src);
        if !closed {
            return;
        }
        let (fi, fb) = crate::checker::cache::tenure_slot(k);
        if self.tc_cache.whnf_store_filter[fi] & fb != 0
            && self.tc_cache.whnf_store.get(&k).is_some()
        {
            return;
        }
        let ai = crate::checker::cache::admit_slot(k);
        let seen = &mut self.tc_cache.whnf_admit[ai];
        if *seen < WHNF_ADMIT_THRESHOLD {
            *seen = seen.saturating_add(1);
            return;
        }
        let Ok((full, verified)) = self.global_key(src, depth) else {
            return;
        };
        if !verified {
            return;
        }
        let Some(hk) = self.shallow_head_key(src) else {
            return;
        };
        let source = self.quote(depth, src);
        if self.ctx.loose(source) != 0 {
            return;
        }
        let q = self.quote(0, res);
        let (hi, hb) = crate::checker::cache::tenure_slot(hk);
        self.tc_cache.whnf_head_filter[hi] |= hb;
        self.tc_cache.whnf_store_filter[fi] |= fb;
        self.tc_cache.whnf_store.insert(k, (full, source, q));
    }

    #[inline]
    fn shallow_head_key(&self, v: V) -> Option<u64> {
        let head = |tag: KeyTag, n: NameId, ls: LevelsId| {
            kmix(tag.u64(), kmix(u64::from(n.raw()), u64::from(ls.raw())))
        };
        let (h, spine) = match self.val(v) {
            Value::Unfold { head: u, spine, .. } => (head(KeyTag::Unfold, u.name, u.levels), spine),
            Value::Rigid {
                head: h @ (RigidHead::Recursor(n, ls) | RigidHead::QuotConst(n, ls)),
                spine,
                ..
            } => (head(h.tag(), n, ls), spine),
            _ => return None,
        };
        Some(kmix(h, u64::from(self.vals().spine_len(spine))))
    }

    #[inline]
    pub(super) fn store_lookup(&mut self, depth: u32, v: V) -> Option<V> {
        let hk = self.shallow_head_key(v)?;
        let (hi, hb) = crate::checker::cache::tenure_slot(hk);
        if self.tc_cache.whnf_head_filter[hi] & hb == 0 {
            return None;
        }
        if !self.vals_mut().is_closed(v) {
            return None;
        }
        let k = self.vals_mut().digest(v);
        let (fi, fb) = crate::checker::cache::tenure_slot(k);
        if self.tc_cache.whnf_store_filter[fi] & fb == 0 {
            return None;
        }
        let (full, source, e) = self.tc_cache.whnf_store.get(&k)?;
        let (mine, verified) = self.global_key(v, depth).ok()?;
        if !verified || mine != full {
            return None;
        }
        if self.quote(depth, v) != source {
            return None;
        }
        let env = EMPTY_ENV;
        Some(self.eval(depth, env, e))
    }

    fn global_key(&mut self, v: V, depth: u32) -> Result<(u128, bool), u8> {
        memo!(
            self.tc_cache.global_value_cache,
            (v, depth),
            self.global_key_uncached(v, depth)
        )
    }

    fn global_key_uncached(&mut self, v: V, depth: u32) -> Result<(u128, bool), u8> {
        match self.val(v) {
            Value::Sort { level, .. } => {
                Ok((mix(KeyTag::Sort.u128(), u128::from(level.raw())), true))
            }
            Value::NatLit { lit, .. } => {
                Ok((mix(KeyTag::NatLit.u128(), u128::from(lit.raw())), true))
            }
            Value::StrLit { lit, .. } => {
                Ok((mix(KeyTag::StrLit.u128(), u128::from(lit.raw())), true))
            }
            Value::Rigid { head, spine, .. } => {
                let (h, c) = match head {
                    RigidHead::BVar(lvl, ty) => {
                        if lvl >= depth {
                            return Err(FAIL_DEPTH);
                        }
                        let (t, _) = self.global_key(ty, depth)?;
                        (
                            mix(mix(KeyTag::BVar.u128(), u128::from(depth - 1 - lvl)), t),
                            false,
                        )
                    }
                    RigidHead::Axiom(n, ls)
                    | RigidHead::Ctor(n, ls)
                    | RigidHead::Recursor(n, ls)
                    | RigidHead::QuotConst(n, ls)
                    | RigidHead::Inductive(n, ls) => (head_key(head.tag(), n, ls), true),
                };
                self.spine_key(h, c, spine, depth)
            }
            Value::Unfold { head, spine, .. } => {
                let h = head_key(KeyTag::Unfold, head.name, head.levels);
                self.spine_key(h, true, spine, depth)
            }
            Value::Lam {
                binder_type, body, ..
            } => {
                let h = mix(KeyTag::Lam.u128(), u128::from(binder_type.raw()));
                self.closure_key(h, body, depth)
            }
            Value::Pi { domain, body, .. } => {
                let (d, dc) = self.global_key(domain, depth)?;
                let (k, cc) = self.closure_key(mix(KeyTag::Pi.u128(), d), body, depth)?;
                Ok((k, dc && cc))
            }
        }
    }

    fn closure_key(&mut self, tag: u128, clo: Closure, depth: u32) -> Result<(u128, bool), u8> {
        if clo.ctx.is_some() {
            return Err(FAIL_CLOSURE);
        }
        let acc = mix(tag, u128::from(clo.body.raw()));
        self.env_key(acc, true, clo.env, depth, clo.loose.saturating_sub(1))
    }

    fn env_key(
        &mut self,
        acc: u128,
        closed: bool,
        env: E,
        depth: u32,
        count: u16,
    ) -> Result<(u128, bool), u8> {
        let mut acc = acc;
        let mut closed = closed;
        if let Some(ls) = self.vals().env_lsub(env) {
            let ls = self.vals().lsub(ls);
            acc = mix(mix(acc, u128::from(ls.ks.raw())), u128::from(ls.vs.raw()));
        }
        for i in 0..count {
            if let Some(slot) = self.vals().env_lookup(env, i) {
                let (k, c) = self.global_key(slot, depth)?;
                acc = mix(mix(acc, u128::from(i)), k);
                closed &= c;
            }
        }
        Ok((acc, closed))
    }

    fn spine_key(
        &mut self,
        head: u128,
        closed: bool,
        s: S,
        depth: u32,
    ) -> Result<(u128, bool), u8> {
        let mut acc = head;
        let mut closed = closed;
        for elim in self.vals().spine_to_vec(s) {
            acc = match elim.view() {
                ElimView::App(a) => {
                    let (k, c) = self.global_key(a, depth)?;
                    closed &= c;
                    mix(acc, k)
                }
                ElimView::Proj { ty_name, idx } => mix(
                    mix(acc, u128::from(ty_name.raw())),
                    u128::from(idx) | (1 << 60),
                ),
            };
        }
        Ok((acc, closed))
    }
}
