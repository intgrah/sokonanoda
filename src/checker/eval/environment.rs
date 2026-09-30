use crate::checker::cache::{hashcons, memo};
use crate::checker::tc::TypeChecker;
use crate::checker::value::{
    self, Closure, E, Elim, ElimView, KeyTag, RigidHead, S, Spine, V, Value,
};
use crate::term::expr::Expr;
use crate::term::hash::GOLDEN;
use crate::term::ptr::{ExprPtr, Id, LevelsPtr, NamePtr};
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
fn elim_key<'a>(elim: &Elim<'a>) -> u64 {
    const _: () = assert!(std::mem::align_of::<Value<'static>>() >= 8);
    elim.raw()
}

impl<'x, 't, 'p> TypeChecker<'x, 't, 'p> {
    #[inline]
    pub(crate) fn mk_bvar_hc(&mut self, level: u32, ty: V<'t>) -> V<'t> {
        memo!(self.tc_cache.bvar_hc, (level, Id::of(ty)), {
            let empty = self.empty_spine();
            let v = value::mk_bvar_with_empty(self.arena, level, ty, empty);
            v.mark_canonical();
            v
        })
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

    pub(crate) fn env_extend(&mut self, parent: E<'t>, v: V<'t>) -> E<'t> {
        hashcons!(
            self.tc_cache.env_hc,
            (Id::of(parent), Id::of(v)),
            value::env_extend(self.arena, parent, v)
        )
    }

    fn intern_frame(
        &mut self,
        hash: u64,
        mask: u64,
        slots: &[V<'t>],
        lsub: Option<&'t value::LevelSub<'t>>,
    ) -> E<'t> {
        let lsub_id = lsub.map(Id::of);
        if let Some(e) = self.tc_cache.frames.find(hash, |e: &E<'t>| match e {
            value::Env::Framed {
                mask: m,
                slots: sl,
                lsub: l,
                ..
            } => {
                *m == mask
                    && l.map(Id::of) == lsub_id
                    && sl.len() == slots.len()
                    && sl.iter().zip(slots).all(|(a, b)| std::ptr::eq(*a, *b))
            }
            _ => false,
        }) {
            return e;
        }
        let len = 64 - mask.leading_zeros();
        let e: E<'t> = self.arena.alloc(value::Env::Framed {
            mask,
            slots: self.arena.alloc_slice_copy(slots),
            lsub,
            hash,
            len,
            prune: std::cell::Cell::new((0, None)),
        });
        self.tc_cache
            .frames
            .insert_unique(hash, e, |e| e.get_hash());
        e
    }

    fn lsub_base(&mut self, lsub: Option<&'t value::LevelSub<'t>>) -> E<'t> {
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
        debug_assert_eq!(
            self.ctx.read_levels(ks).len(),
            self.ctx.read_levels(vs).len()
        );
        if ks == vs || self.ctx.read_levels(ks).is_empty() {
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
            value::Env::Cons { prune, .. } | value::Env::WideFramed { prune, .. } => {
                let (m, r) = prune.get();
                if m == mask
                    && let Some(r) = r
                {
                    return r;
                }
            }
        }
        let slot = (((Id::of(e).addr() as u64).wrapping_mul(GOLDEN)
            ^ mask.wrapping_mul(0xD6E8FEB86659FD93))
            >> crate::checker::cache::PRUNE_DM_SHIFT) as usize;
        let ent = self.tc_cache.prune_dm[slot];
        if ent.0 == Some(Id::of(e))
            && ent.1 == mask
            && let Some(hit) = ent.2
        {
            match e {
                value::Env::Cons { prune, .. }
                | value::Env::Framed { prune, .. }
                | value::Env::WideFramed { prune, .. } => prune.set((mask, Some(hit))),
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
        let mut slots_hash = e.lsub().map_or(0, |l| Id::of(l).addr() as u64);
        let mut n = 0usize;
        let mut out_mask = 0u64;
        let mut rem = mask;
        let mut consumed = 0u32;
        let mut cur = e;
        while rem != 0 {
            match cur {
                value::Env::Nil { .. } => break,
                value::Env::Framed {
                    mask: fmask, slots, ..
                } => {
                    let limit = 64 - consumed;
                    let bound = if limit >= 64 {
                        u64::MAX
                    } else {
                        (1u64 << limit) - 1
                    };
                    let m2 = rem & *fmask & bound;
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
                    break;
                }
                value::Env::WideFramed { data, .. } => {
                    for (&idx, &v) in data.indices.iter().zip(data.slots) {
                        if u32::from(idx) >= 64 - consumed {
                            break;
                        }
                        if (rem >> idx) & 1 != 0 {
                            buf[n].write(v);
                            slots_hash = slots_hash
                                .wrapping_mul(GOLDEN)
                                .wrapping_add(Id::of(v).addr() as u64);
                            out_mask |= 1u64 << (u32::from(idx) + consumed);
                            n += 1;
                        }
                    }
                    break;
                }
                value::Env::Cons { v, parent, .. } => {
                    if rem & 1 != 0 {
                        buf[n].write(*v);
                        slots_hash = slots_hash
                            .wrapping_mul(GOLDEN)
                            .wrapping_add(Id::of(*v).addr() as u64);
                        out_mask |= 1u64 << consumed;
                        n += 1;
                    }
                    rem >>= 1;
                    if rem == 0 {
                        break;
                    }
                    consumed += 1;
                    cur = parent;
                }
            }
        }
        let slots: &[V<'t>] =
            unsafe { std::slice::from_raw_parts(buf.as_ptr().cast::<V<'t>>(), n) };
        let lsub = e.lsub();
        let hash = out_mask.wrapping_mul(GOLDEN).wrapping_add(slots_hash);
        let r = self.intern_frame(hash, out_mask, slots, lsub);
        self.tc_cache.prune_dm[slot] = (Some(Id::of(e)), mask, Some(r));
        match e {
            value::Env::Cons { prune, .. }
            | value::Env::Framed { prune, .. }
            | value::Env::WideFramed { prune, .. } => prune.set((mask, Some(r))),
            value::Env::Nil { .. } => {}
        }
        r
    }

    #[inline(always)]
    pub(crate) fn key_env(&mut self, env: E<'t>, e: ExprPtr<'t>) -> E<'t> {
        let k = e.num_loose_bvars();
        if k == 0 {
            return self.lsub_base(env.lsub());
        }
        if k > 64 {
            return self.prune_wide_env(env, e);
        }
        self.prune_env(env, e.as_ref().fv_mask())
    }

    fn wide_fvars(&mut self, e: ExprPtr<'t>) -> &'t [u16] {
        if let Some(indices) = self.tc_cache.wide_fvars.get(&e) {
            return indices;
        }
        let mut indices = smallvec::SmallVec::<[u16; 16]>::new();
        if e.num_loose_bvars() <= 64 {
            let mut mask = e.as_ref().fv_mask();
            while mask != 0 {
                indices.push(u16::try_from(mask.trailing_zeros()).unwrap());
                mask &= mask - 1;
            }
        } else {
            match *e.as_ref() {
                Expr::Var { dbj_idx, .. } => indices.push(dbj_idx),
                Expr::App { fun, arg, .. } => {
                    indices.extend_from_slice(self.wide_fvars(fun));
                    indices.extend_from_slice(self.wide_fvars(arg));
                }
                Expr::Pi {
                    binder_type, body, ..
                }
                | Expr::Lambda {
                    binder_type, body, ..
                } => {
                    indices.extend_from_slice(self.wide_fvars(binder_type));
                    indices.extend(
                        self.wide_fvars(body)
                            .iter()
                            .filter_map(|i| i.checked_sub(1)),
                    );
                }
                Expr::Let { data, .. } => {
                    indices.extend_from_slice(self.wide_fvars(data.binder_type));
                    indices.extend_from_slice(self.wide_fvars(data.val));
                    indices.extend(
                        self.wide_fvars(data.body)
                            .iter()
                            .filter_map(|i| i.checked_sub(1)),
                    );
                }
                Expr::Proj { structure, .. } => {
                    indices.extend_from_slice(self.wide_fvars(structure))
                }
                Expr::Sort { .. }
                | Expr::Const { .. }
                | Expr::StringLit { .. }
                | Expr::NatLit { .. } => {}
            }
            indices.sort_unstable();
            indices.dedup();
        }
        let indices = self.arena.alloc_slice_copy(&indices);
        self.tc_cache.wide_fvars.insert(e, indices);
        indices
    }

    #[inline(never)]
    fn prune_wide_env(&mut self, env: E<'t>, e: ExprPtr<'t>) -> E<'t> {
        let key = (Id::of(env), e);
        if let Some(r) = self.tc_cache.wide_prune.get(&key) {
            return r;
        }
        let wanted = self.wide_fvars(e);
        let mut indices = smallvec::SmallVec::<[u16; 16]>::new();
        let mut slots = smallvec::SmallVec::<[V<'t>; 16]>::new();
        let mut cur = env;
        let mut consumed = 0;
        let lsub = env.lsub();
        let mut slots_hash = lsub.map_or(0, |l| Id::of(l).addr() as u64);
        for &idx in wanted {
            while consumed < idx {
                let value::Env::Cons { parent, .. } = cur else {
                    break;
                };
                cur = parent;
                consumed += 1;
            }
            if let Some(v) = cur.lookup(idx - consumed) {
                indices.push(idx);
                slots.push(v);
                slots_hash = slots_hash
                    .wrapping_mul(GOLDEN)
                    .wrapping_add(Id::of(v).addr() as u64);
            }
        }
        let r = match indices.last() {
            None => self.lsub_base(lsub),
            Some(&last) if last < 64 => {
                let mask = indices.iter().fold(0u64, |mask, i| mask | (1u64 << i));
                let hash = mask.wrapping_mul(GOLDEN).wrapping_add(slots_hash);
                self.intern_frame(hash, mask, &slots, lsub)
            }
            Some(&last) => {
                let hash = indices.iter().fold(slots_hash, |h, i| {
                    h.wrapping_mul(GOLDEN).wrapping_add(u64::from(*i))
                });
                if let Some(r) = self.tc_cache.frames.find(hash, |r| match r {
                    value::Env::WideFramed { data, lsub: ls, .. } => {
                        data.indices == indices.as_slice()
                            && ls.map(Id::of) == lsub.map(Id::of)
                            && data
                                .slots
                                .iter()
                                .zip(&slots)
                                .all(|(a, b)| std::ptr::eq(*a, *b))
                    }
                    _ => false,
                }) {
                    *r
                } else {
                    let data = self.arena.alloc(value::WideFrame {
                        indices: self.arena.alloc_slice_copy(&indices),
                        slots: self.arena.alloc_slice_copy(&slots),
                    });
                    let r: E<'t> = self.arena.alloc(value::Env::WideFramed {
                        data,
                        lsub,
                        hash,
                        len: u32::from(last) + 1,
                        prune: std::cell::Cell::new((0, None)),
                    });
                    self.tc_cache
                        .frames
                        .insert_unique(hash, r, |r| r.get_hash());
                    r
                }
            }
        };
        self.tc_cache.wide_prune.insert(key, r);
        r
    }

    #[inline]
    pub(super) fn spine_snoc_hc(&mut self, prev: S<'t>, elim: Elim<'t>) -> S<'t> {
        hashcons!(self.tc_cache.spine_hc, (Id::of(prev), elim_key(&elim)), {
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
    fn mk_lam_hc(&mut self, binder_type: ExprPtr<'t>, body: Closure<'t>) -> V<'t> {
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

    #[inline]
    pub(super) fn canonicalize_for_spine(&mut self, v: V<'t>) -> V<'t> {
        if v.is_canonical() {
            return v;
        }
        if matches!(v, Value::Thunk { .. }) {
            return v;
        }
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
            Value::Thunk { .. } => v,
        }
    }

    #[inline]
    fn mk_pi_hc(&mut self, domain: V<'t>, body: Closure<'t>) -> V<'t> {
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
