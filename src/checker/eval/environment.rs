// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::{hashcons, memo};
use crate::checker::tc::TypeChecker;
use crate::checker::value::{
    self, Closure, E, Elim, ElimView, KeyTag, RigidHead, S, Spine, V, Value,
};
use crate::term::hash::GOLDEN;
use crate::term::ptr::{BigUintPtr, ExprPtr, Id, LevelPtr, LevelsPtr, NamePtr, StringPtr};
use std::cell::OnceCell;

#[inline]
fn rigid_head_key(head: RigidHead<'_>) -> (KeyTag, u64, u64) {
    match head {
        RigidHead::BVar(lvl, ty) => (KeyTag::BVar, u64::from(lvl), Id::of(ty).addr() as u64),
        RigidHead::Axiom(n, l)
        | RigidHead::Ctor(n, l)
        | RigidHead::Recursor(n, l)
        | RigidHead::QuotConst(n, l)
        | RigidHead::Inductive(n, l) => (head.tag(), n.get_hash(), l.get_hash()),
    }
}

#[inline]
fn elim_key(elim: Elim<'_>) -> u64 {
    const _: () = assert!(std::mem::align_of::<Value<'static>>() >= 8);
    elim.raw()
}

impl<'t> TypeChecker<'_, 't, '_> {
    #[inline]
    pub(crate) fn mk_bvar_hc(&mut self, level: u32, ty: V<'t>) -> V<'t> {
        memo!(self.tc_cache.bvar_hc, (level, Id::of(ty)), {
            let empty = self.empty_spine();
            let v = value::mk_bvar_with_empty(self.arena, level, ty, empty);
            v.mark_canonical();
            v
        })
    }

    pub(crate) fn mk_sort_hc(&mut self, level: LevelPtr<'t>) -> V<'t> {
        memo!(
            self.tc_cache.content_hc,
            (KeyTag::Sort, level.get_hash()),
            value::mk_sort(self.arena, level)
        )
    }

    pub(crate) fn mk_natlit_hc(&mut self, ptr: BigUintPtr<'t>) -> V<'t> {
        memo!(
            self.tc_cache.content_hc,
            (KeyTag::NatLit, ptr.get_hash()),
            value::mk_natlit(self.arena, ptr)
        )
    }

    pub(crate) fn mk_strlit_hc(&mut self, ptr: StringPtr<'t>) -> V<'t> {
        memo!(
            self.tc_cache.content_hc,
            (KeyTag::StrLit, ptr.get_hash()),
            value::mk_strlit(self.arena, ptr)
        )
    }

    pub(crate) fn mk_head_hc(&mut self, head: RigidHead<'t>) -> V<'t> {
        if let RigidHead::BVar(level, ty) = head {
            return self.mk_bvar_hc(level, ty);
        }
        let empty = self.empty_spine();
        self.mk_rigid_hc(head, empty)
    }

    pub(super) fn mk_unfold_hc(
        &mut self,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
        spine: S<'t>,
        head_value: &'t OnceCell<V<'t>>,
    ) -> V<'t> {
        memo!(
            self.tc_cache.unfold_hc,
            (Id::of(head_value), Id::of(spine)),
            {
                let u = value::mk_unfold(self.arena, name, levels, spine, head_value);
                if spine.is_canonical() {
                    u.mark_canonical();
                }
                u
            }
        )
    }

    #[inline(always)]
    pub(crate) fn env_extend(&mut self, parent: E<'t>, v: V<'t>) -> E<'t> {
        match self.tc_cache.env_hc.get(&(Id::of(parent), Id::of(v))) {
            Some(e) => e,
            None => self.env_new(parent, v),
        }
    }

    #[inline(never)]
    fn env_new(&mut self, parent: E<'t>, v: V<'t>) -> E<'t> {
        let e = value::env_extend(self.arena, parent, v);
        self.tc_cache.env_hc.insert((Id::of(parent), Id::of(v)), e);
        e
    }

    fn intern_frame(
        &mut self,
        slots_hash: u64,
        near: u64,
        slots: &[V<'t>],
        cut: u32,
        rest: Option<E<'t>>,
        lsub: Option<&'t value::LevelSub<'t>>,
    ) -> E<'t> {
        let mut hash = near.wrapping_mul(GOLDEN).wrapping_add(slots_hash);
        let (mask, cut, len) = match rest {
            Some(r) => {
                hash = (hash.rotate_left(29) ^ (Id::of(r).addr() as u64))
                    .wrapping_mul(GOLDEN)
                    .wrapping_add(u64::from(cut));
                (near | value::FAR, cut, cut + r.len())
            }
            None => (near, value::NEAR, 64 - near.leading_zeros()),
        };
        let found = self.tc_cache.frames.find(hash);
        if let Ok(e) = found
            && let value::Env::Framed {
                mask: m,
                slots: sl,
                cut: c,
                rest: r,
                lsub: l,
                ..
            } = e
            && *m == mask
            && u32::from(*c) == cut
            && r.map(Id::of) == rest.map(Id::of)
            && l.map(Id::of) == lsub.map(Id::of)
            && sl.len() == slots.len()
            && sl.iter().zip(slots).all(|(a, b)| std::ptr::eq(*a, *b))
        {
            return e;
        }
        let e: E<'t> = self.arena.alloc(value::Env::Framed {
            mask,
            slots: copy_slots(self.arena, slots),
            cut: u8::try_from(cut).expect("a frame spans at most 63 positions"),
            rest,
            lsub,
            len,
            prune: std::cell::Cell::new((0, None)),
        });
        if let Err(vacant) = found {
            self.tc_cache.frames.insert_at(vacant, hash, e);
        }
        e
    }

    fn frame_without(
        &mut self,
        dropped: u32,
        mask: u64,
        slots: &'t [V<'t>],
        cut: u32,
        rest: Option<E<'t>>,
        lsub: Option<&'t value::LevelSub<'t>>,
    ) -> Option<E<'t>> {
        let near = (mask & !value::FAR) >> dropped;
        if near == 0 && rest.is_none() {
            return None;
        }
        let skipped = (mask & ((1u64 << dropped) - 1)).count_ones() as usize;
        let kept = &slots[skipped..];
        let slots_hash = kept
            .iter()
            .fold(lsub.map_or(0, |l| Id::of(l).addr() as u64), |h, v| {
                h.wrapping_mul(GOLDEN)
                    .wrapping_add(Id::of(*v).addr() as u64)
            });
        Some(self.intern_frame(slots_hash, near, kept, cut - dropped, rest, lsub))
    }

    pub(super) fn lsub_base(&mut self, lsub: Option<&'t value::LevelSub<'t>>) -> E<'t> {
        let Some(ls) = lsub else {
            return self.tc_cache.empty_env;
        };
        let id = Id::of(ls);
        memo!(
            self.tc_cache.lsub_bases,
            id,
            self.arena.alloc(value::Env::Nil {
                lsub,
                hash: id.addr() as u64,
            })
        )
    }

    fn intern_level_sub(
        &mut self,
        ks: LevelsPtr<'t>,
        vs: LevelsPtr<'t>,
    ) -> &'t value::LevelSub<'t> {
        memo!(
            self.tc_cache.level_subs,
            (ks, vs),
            self.arena.alloc(value::LevelSub { ks, vs })
        )
    }

    pub(crate) fn eval_inst(
        &mut self,
        ex: ExprPtr<'t>,
        ks: LevelsPtr<'t>,
        vs: LevelsPtr<'t>,
    ) -> V<'t> {
        debug_assert_eq!(ks.as_ref().len(), vs.as_ref().len());
        if ks == vs || ks.as_ref().is_empty() {
            let empty = self.empty_env();
            return self.eval(0, empty, ex);
        }
        let ls = self.intern_level_sub(ks, vs);
        let base = self.lsub_base(Some(ls));
        self.eval(0, base, ex)
    }

    #[inline]
    fn prune_env(&mut self, e: E<'t>, mask: u64) -> E<'t> {
        if mask == 0 {
            return self.lsub_base(e.lsub());
        }
        match e {
            value::Env::Nil { .. } => return e,
            value::Env::Framed { mask: m, prune, .. } => {
                if *m & mask == *m {
                    return e;
                }
                let (m, r) = prune.get();
                if m == mask
                    && let Some(r) = r
                {
                    return r;
                }
            }
            value::Env::Cons { prune, .. } => {
                let (m, r) = prune.get();
                if m == mask
                    && let Some(r) = r
                {
                    return r;
                }
            }
        }
        let slot = (((Id::of(e).addr() as u64).wrapping_mul(GOLDEN)
            ^ mask.wrapping_mul(0xD6E8_FEB8_6659_FD93))
            >> crate::checker::cache::PRUNE_DM_SHIFT) as usize;
        let ent = self.tc_cache.prune_dm[slot];
        if ent.0 == Some(Id::of(e))
            && ent.1 == mask
            && let Some(hit) = ent.2
        {
            match e {
                value::Env::Cons { prune, .. } | value::Env::Framed { prune, .. } => {
                    prune.set((mask, Some(hit)));
                }
                value::Env::Nil { .. } => {}
            }
            return hit;
        }
        self.prune_env_cold(e, mask, slot)
    }

    #[inline(never)]
    fn prune_env_cold(&mut self, e: E<'t>, mask: u64, slot: usize) -> E<'t> {
        let mut buf: [std::mem::MaybeUninit<V<'t>>; 64] =
            [const { std::mem::MaybeUninit::uninit() }; 64];
        let lsub = e.lsub();
        let mut slots_hash = lsub.map_or(0, |l| Id::of(l).addr() as u64);
        let mut n = 0usize;
        let mut out_mask = 0u64;
        let keep_far = mask & value::FAR != 0;
        let mut rem = mask & !value::FAR;
        let mut consumed = 0u32;
        let mut cur = e;
        let mut rest = None;
        loop {
            if consumed == value::NEAR {
                if keep_far {
                    rest = match cur {
                        value::Env::Nil { .. } | value::Env::Framed { mask: 0, .. } => None,
                        _ => Some(cur),
                    };
                }
                break;
            }
            if rem == 0 && !keep_far {
                break;
            }
            match cur {
                value::Env::Nil { .. } => break,
                value::Env::Framed {
                    mask: fmask,
                    slots,
                    cut,
                    rest: frest,
                    ..
                } => {
                    let cut = u32::from(*cut);
                    let taken = cut.min(value::NEAR - consumed);
                    let m2 = rem & *fmask & ((1u64 << taken) - 1);
                    out_mask |= m2 << consumed;
                    let mut sel = select_ranks(m2, *fmask);
                    while sel != 0 {
                        let i = sel.trailing_zeros() as usize;
                        sel &= sel - 1;
                        let sv = slots[i];
                        buf[n].write(sv);
                        slots_hash = slots_hash
                            .wrapping_mul(GOLDEN)
                            .wrapping_add(Id::of(sv).addr() as u64);
                        n += 1;
                    }
                    if taken < cut {
                        if keep_far {
                            rest = self.frame_without(taken, *fmask, slots, cut, *frest, lsub);
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
                value::Env::Cons { v, parent, .. } => {
                    if rem & 1 != 0 {
                        buf[n].write(*v);
                        slots_hash = slots_hash
                            .wrapping_mul(GOLDEN)
                            .wrapping_add(Id::of(*v).addr() as u64);
                        out_mask |= 1u64 << consumed;
                        n += 1;
                        rem >>= 1;
                        consumed += 1;
                        cur = parent;
                        continue;
                    }
                    let unrequested = rem.trailing_zeros().min(value::NEAR - consumed);
                    let mut hops = 0;
                    while hops < unrequested
                        && let value::Env::Cons { parent, .. } = cur
                    {
                        cur = parent;
                        hops += 1;
                    }
                    rem >>= hops;
                    consumed += hops;
                }
            }
        }
        let slots: &[V<'t>] =
            unsafe { std::slice::from_raw_parts(buf.as_ptr().cast::<V<'t>>(), n) };
        let r = self.intern_frame(slots_hash, out_mask, slots, value::NEAR, rest, lsub);
        self.tc_cache.prune_dm[slot] = (Some(Id::of(e)), mask, Some(r));
        match e {
            value::Env::Cons { prune, .. } | value::Env::Framed { prune, .. } => {
                prune.set((mask, Some(r)));
            }
            value::Env::Nil { .. } => {}
        }
        r
    }

    #[inline(always)]
    pub(crate) fn key_env(&mut self, env: E<'t>, e: ExprPtr<'t>) -> E<'t> {
        if e.num_loose_bvars() == 0 {
            return self.lsub_base(env.lsub());
        }
        self.prune_env(env, e.as_ref().fv_mask())
    }

    #[inline]
    pub(super) fn spine_snoc_hc(&mut self, prev: S<'t>, elim: Elim<'t>) -> S<'t> {
        hashcons!(self.tc_cache.spine_hc, (Id::of(prev), elim_key(elim)), {
            let s = value::spine_snoc(self.arena, prev, elim);
            let canon = prev.is_canonical()
                && match elim.view() {
                    ElimView::App(a) => a.is_canonical(),
                    ElimView::Proj { .. } => true,
                };
            if canon {
                s.mark_canonical();
            }
            s
        })
    }

    #[inline]
    pub(super) fn mk_rigid_hc(&mut self, head: RigidHead<'t>, spine: S<'t>) -> V<'t> {
        let hk = rigid_head_key(head);
        hashcons!(self.tc_cache.rigid_hc, (hk.0, hk.1, hk.2, Id::of(spine)), {
            let v = value::mk_rigid(self.arena, head, spine);
            if spine.is_canonical() {
                v.mark_canonical();
            }
            v
        })
    }

    #[inline]
    pub(crate) fn mk_lam_hc(&mut self, binder_type: ExprPtr<'t>, body: Closure<'t>) -> V<'t> {
        debug_assert!(body.ctx.is_none());
        hashcons!(
            self.tc_cache.lam_hc,
            (binder_type, Id::of(body.env), body.body),
            {
                let v = value::mk_lam(self.arena, binder_type, body);
                v.mark_canonical();
                v
            }
        )
    }

    #[inline(always)]
    pub(super) fn canonicalize_for_spine(&mut self, v: V<'t>) -> V<'t> {
        if v.is_canonical() {
            v
        } else {
            self.canonicalize(v)
        }
    }

    #[inline(never)]
    fn canonicalize(&mut self, v: V<'t>) -> V<'t> {
        memo!(self.tc_cache.canon_cache, Id::of(v), {
            let c = self.canon_compute(v);
            c.mark_canonical();
            c
        })
    }

    fn canon_content(&mut self, tag: KeyTag, content: u64, v: V<'t>) -> V<'t> {
        memo!(self.tc_cache.content_hc, (tag, content), v)
    }

    fn canon_spine(&mut self, spine: S<'t>) -> S<'t> {
        match spine {
            Spine::Empty => spine,
            Spine::Snoc { prev, elim, .. } => {
                let cprev = self.canon_spine(prev);
                let celim = match elim.view() {
                    ElimView::App(a) => {
                        let ca = self.canonicalize_for_spine(a);
                        Elim::app(ca)
                    }
                    ElimView::Proj { ty_name, idx } => Elim::proj(ty_name, idx),
                };
                self.spine_snoc_hc(cprev, celim)
            }
        }
    }

    fn canon_compute(&mut self, v: V<'t>) -> V<'t> {
        match v {
            Value::Lam {
                binder_type, body, ..
            } => self.mk_lam_hc(*binder_type, *body),
            Value::Pi { domain, body, .. } => self.mk_pi_hc(domain, *body),
            Value::Sort { level, .. } => self.canon_content(KeyTag::Sort, level.get_hash(), v),
            Value::NatLit { ptr, .. } => self.canon_content(KeyTag::NatLit, ptr.get_hash(), v),
            Value::StrLit { ptr, .. } => self.canon_content(KeyTag::StrLit, ptr.get_hash(), v),
            Value::Rigid { head, spine, .. } => {
                let cspine = self.canon_spine(spine);
                self.mk_rigid_hc(*head, cspine)
            }
            Value::Unfold {
                head,
                spine,
                head_value,
                ..
            } => {
                let (hn, hl, hv, sp) = (head.name, head.levels, *head_value, *spine);
                let cspine = self.canon_spine(sp);
                self.mk_unfold_hc(hn, hl, cspine, hv)
            }
        }
    }

    #[inline]
    pub(crate) fn mk_pi_hc(&mut self, domain: V<'t>, body: Closure<'t>) -> V<'t> {
        let key = (
            Id::of(domain),
            Id::of(body.env),
            body.body,
            body.ctx.map(Id::of),
        );
        hashcons!(self.tc_cache.pi_hc, key, {
            let v = value::mk_pi(self.arena, domain, body);
            v.mark_canonical();
            v
        })
    }
}

#[inline(always)]
fn copy_slots<'t>(arena: &'t bumpalo::Bump, slots: &[V<'t>]) -> &'t [V<'t>] {
    #[inline(always)]
    fn fixed<'t, const N: usize>(arena: &'t bumpalo::Bump, slots: &[V<'t>]) -> &'t [V<'t>] {
        let array: [V<'t>; N] = slots.try_into().expect("slot count matches the arm");
        arena.alloc(array)
    }
    match slots.len() {
        1 => fixed::<1>(arena, slots),
        2 => fixed::<2>(arena, slots),
        3 => fixed::<3>(arena, slots),
        4 => fixed::<4>(arena, slots),
        5 => fixed::<5>(arena, slots),
        6 => fixed::<6>(arena, slots),
        7 => fixed::<7>(arena, slots),
        8 => fixed::<8>(arena, slots),
        _ => arena.alloc_slice_copy(slots),
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "bmi2")]
unsafe fn pext(a: u64, m: u64) -> u64 {
    std::arch::x86_64::_pext_u64(a, m)
}

#[inline]
fn select_ranks(sub: u64, sup: u64) -> u64 {
    #[cfg(target_arch = "x86_64")]
    if std::is_x86_feature_detected!("bmi2") {
        return unsafe { pext(sub, sup) };
    }
    let mut out = 0u64;
    let mut f = sup;
    let mut rank = 0u32;
    while f != 0 {
        let j = f.trailing_zeros();
        f &= f - 1;
        if (sub >> j) & 1 != 0 {
            out |= 1u64 << rank;
        }
        rank += 1;
    }
    out
}
