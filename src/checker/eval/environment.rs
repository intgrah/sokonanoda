use crate::checker::tc::TypeChecker;
use crate::checker::value::{self, Closure, Elim, ElimView, RigidHead, Spine, Value, E, S, V};
use crate::term::expr::Expr;
use crate::term::ptr::{ExprPtr, LevelsPtr, NamePtr};
use std::cell::OnceCell;
use std::collections::hash_map::Entry;

#[inline]
fn rigid_head_key<'a>(head: &RigidHead<'a>) -> (u8, u64, u64) {
    match *head {
        RigidHead::BVar(lvl, ty) => (0, u64::from(lvl), ty as *const Value<'a> as u64),
        RigidHead::Axiom(n, l) => (2, n.get_hash(), l.get_hash()),
        RigidHead::Ctor(n, l) => (3, n.get_hash(), l.get_hash()),
        RigidHead::Recursor(n, l) => (4, n.get_hash(), l.get_hash()),
        RigidHead::QuotConst(n, l) => (5, n.get_hash(), l.get_hash()),
        RigidHead::Inductive(n, l) => (6, n.get_hash(), l.get_hash()),
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
        let key = (level, ty as *const Value<'t> as usize);
        if let Some(v) = self.tc_cache.bvar_hc.get(&key) {
            return v;
        }
        let empty = self.empty_spine();
        let v = value::mk_bvar_with_empty(self.arena, level, ty, empty);
        v.mark_canonical();
        self.tc_cache.bvar_hc.insert(key, v);
        v
    }

    pub(super) fn mk_unfold_hc(
        &mut self,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
        spine: S<'t>,
        head_value: &'t OnceCell<V<'t>>,
    ) -> V<'t> {
        let key = (
            head_value as *const OnceCell<V<'t>> as usize,
            spine as *const Spine<'t> as usize,
        );
        if let Some(u) = self.tc_cache.unfold_hc.get(&key) {
            return u;
        }
        let u = value::mk_unfold(self.arena, name, levels, spine, head_value);
        if spine.is_canonical() {
            u.mark_canonical();
        }
        self.tc_cache.unfold_hc.insert(key, u);
        u
    }

    pub(crate) fn env_extend(&mut self, parent: E<'t>, v: V<'t>) -> E<'t> {
        let key = (
            parent as *const value::Env<'t> as usize,
            v as *const Value<'t> as usize,
        );
        match self.tc_cache.env_hc.entry(key) {
            Entry::Occupied(o) => o.get(),
            Entry::Vacant(slot) => slot.insert(value::env_extend(self.arena, parent, v)),
        }
    }

    fn intern_frame(
        &mut self,
        hash: u64,
        mask: u64,
        slots: &[V<'t>],
        lsub: Option<&'t value::LevelSub<'t>>,
    ) -> E<'t> {
        let lsub_addr = lsub.map_or(0, |l| l as *const value::LevelSub<'t> as usize);
        if let Some(e) = self.tc_cache.frames.find(hash, |e: &E<'t>| match e {
            value::Env::Framed {
                mask: m,
                slots: sl,
                lsub: l,
                ..
            } => {
                *m == mask
                    && l.map_or(0, |l| l as *const value::LevelSub<'t> as usize) == lsub_addr
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
        let key = ls as *const value::LevelSub<'t> as usize;
        if let Some(e) = self.tc_cache.lsub_bases.get(&key) {
            return e;
        }
        let e: E<'t> = self.arena.alloc(value::Env::Nil {
            lsub,
            hash: key as u64,
        });
        self.tc_cache.lsub_bases.insert(key, e);
        e
    }

    fn intern_level_sub(
        &mut self,
        ks: LevelsPtr<'t>,
        vs: LevelsPtr<'t>,
    ) -> &'t value::LevelSub<'t> {
        if let Some(l) = self.tc_cache.level_subs.get(&(ks, vs)) {
            return l;
        }
        let l: &'t value::LevelSub<'t> = self.arena.alloc(value::LevelSub { ks, vs });
        self.tc_cache.level_subs.insert((ks, vs), l);
        l
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
                if m == mask {
                    if let Some(r) = r {
                        return r;
                    }
                }
            }
            value::Env::Cons { prune, .. } | value::Env::WideFramed { prune, .. } => {
                let (m, r) = prune.get();
                if m == mask {
                    if let Some(r) = r {
                        return r;
                    }
                }
            }
        }
        let slot = (((e as *const value::Env<'t> as usize as u64).wrapping_mul(0x9E3779B97F4A7C15)
            ^ mask.wrapping_mul(0xD6E8FEB86659FD93))
            >> crate::checker::cache::PRUNE_DM_SHIFT) as usize;
        let ent = self.tc_cache.prune_dm[slot];
        if ent.0 == e as *const value::Env<'t> as usize && ent.1 == mask {
            if let Some(hit) = ent.2 {
                match e {
                    value::Env::Cons { prune, .. }
                    | value::Env::Framed { prune, .. }
                    | value::Env::WideFramed { prune, .. } => prune.set((mask, Some(hit))),
                    value::Env::Nil { .. } => {}
                }
                return hit;
            }
        }
        self.prune_env_cold(e, mask, slot)
    }

    #[inline(never)]
    fn prune_env_cold(&mut self, e: E<'t>, mask: u64, slot: usize) -> E<'t> {
        let mut buf: [std::mem::MaybeUninit<V<'t>>; 64] =
            [const { std::mem::MaybeUninit::uninit() }; 64];
        let mut slots_hash = e
            .lsub()
            .map_or(0, |l| l as *const value::LevelSub<'t> as usize as u64);
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
                            .wrapping_mul(0x9E3779B97F4A7C15)
                            .wrapping_add(sv as *const Value<'t> as usize as u64);
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
                                .wrapping_mul(0x9E3779B97F4A7C15)
                                .wrapping_add(v as *const Value<'t> as usize as u64);
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
                            .wrapping_mul(0x9E3779B97F4A7C15)
                            .wrapping_add(*v as *const Value<'t> as usize as u64);
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
        let hash = out_mask
            .wrapping_mul(0x9E3779B97F4A7C15)
            .wrapping_add(slots_hash);
        let r = self.intern_frame(hash, out_mask, slots, lsub);
        self.tc_cache.prune_dm[slot] = (e as *const value::Env<'t> as usize, mask, Some(r));
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
        let key = (env as *const value::Env<'t> as usize, e);
        if let Some(r) = self.tc_cache.wide_prune.get(&key) {
            return r;
        }
        let wanted = self.wide_fvars(e);
        let mut indices = smallvec::SmallVec::<[u16; 16]>::new();
        let mut slots = smallvec::SmallVec::<[V<'t>; 16]>::new();
        let mut cur = env;
        let mut consumed = 0;
        let lsub = env.lsub();
        let mut slots_hash = lsub.map_or(0, |l| l as *const value::LevelSub<'t> as usize as u64);
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
                    .wrapping_mul(0x9E3779B97F4A7C15)
                    .wrapping_add(v as *const Value<'t> as usize as u64);
            }
        }
        let r = match indices.last() {
            None => self.lsub_base(lsub),
            Some(&last) if last < 64 => {
                let mask = indices.iter().fold(0u64, |mask, i| mask | (1u64 << i));
                let hash = mask
                    .wrapping_mul(0x9E3779B97F4A7C15)
                    .wrapping_add(slots_hash);
                self.intern_frame(hash, mask, &slots, lsub)
            }
            Some(&last) => {
                let hash = indices.iter().fold(slots_hash, |h, i| {
                    h.wrapping_mul(0x9E3779B97F4A7C15)
                        .wrapping_add(u64::from(*i))
                });
                let lsub_addr = lsub.map_or(0, |l| l as *const value::LevelSub<'t> as usize);
                if let Some(r) = self.tc_cache.frames.find(hash, |r| match r {
                    value::Env::WideFramed { data, lsub: ls, .. } => {
                        data.indices == indices.as_slice()
                            && ls.map_or(0, |l| l as *const value::LevelSub<'t> as usize)
                                == lsub_addr
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
        let key = (prev as *const Spine<'t> as usize, elim_key(&elim));
        let arena = self.arena;
        match self.tc_cache.spine_hc.entry(key) {
            Entry::Occupied(o) => *o.get(),
            Entry::Vacant(slot) => {
                let s = value::spine_snoc(arena, prev, elim);
                let canon = prev.is_canonical()
                    && match elim.view() {
                        ElimView::App(a) => a.is_canonical(),
                        ElimView::Proj { .. } => true,
                    };
                if canon {
                    s.mark_canonical();
                }
                *slot.insert(s)
            }
        }
    }

    #[inline]
    pub(super) fn mk_rigid_hc(&mut self, head: RigidHead<'t>, spine: S<'t>) -> V<'t> {
        let hk = rigid_head_key(&head);
        let key = (hk.0, hk.1, hk.2, spine as *const Spine<'t> as usize);
        let arena = self.arena;
        match self.tc_cache.rigid_hc.entry(key) {
            Entry::Occupied(o) => *o.get(),
            Entry::Vacant(slot) => {
                let v = value::mk_rigid(arena, head, spine);
                if spine.is_canonical() {
                    v.mark_canonical();
                }
                *slot.insert(v)
            }
        }
    }

    #[inline]
    fn mk_lam_hc(&mut self, binder_type: ExprPtr<'t>, body: Closure<'t>) -> V<'t> {
        debug_assert!(body.ctx.is_none());
        let key = (
            binder_type,
            body.env as *const value::Env<'t> as usize,
            body.body,
        );
        let arena = self.arena;
        match self.tc_cache.lam_hc.entry(key) {
            Entry::Occupied(o) => *o.get(),
            Entry::Vacant(slot) => {
                let v = value::mk_lam(arena, binder_type, body);
                v.mark_canonical();
                *slot.insert(v)
            }
        }
    }

    #[inline]
    pub(super) fn canonicalize_for_spine(&mut self, v: V<'t>) -> V<'t> {
        if v.is_canonical() {
            return v;
        }
        if matches!(v, Value::Thunk { .. }) {
            return v;
        }
        let key = v as *const Value<'t> as usize;
        if let Some(c) = self.tc_cache.canon_cache.get(&key) {
            return c;
        }
        let c = self.canon_compute(v);
        c.mark_canonical();
        self.tc_cache.canon_cache.insert(key, c);
        c
    }

    fn canon_content(&mut self, disc: u8, content: u64, v: V<'t>) -> V<'t> {
        if let Some(c) = self.tc_cache.content_hc.get(&(disc, content)) {
            return c;
        }
        self.tc_cache.content_hc.insert((disc, content), v);
        v
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
            Value::Sort { level, .. } => self.canon_content(0, level.get_hash(), v),
            Value::NatLit { ptr, .. } => self.canon_content(1, ptr.get_hash(), v),
            Value::StrLit { ptr, .. } => self.canon_content(2, ptr.get_hash(), v),
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
            domain as *const Value<'t> as usize,
            body.env as *const value::Env<'t> as usize,
            body.body,
            body.ctx.map_or(0, |c| c as *const value::Ctx<'t> as usize),
        );
        let arena = self.arena;
        match self.tc_cache.pi_hc.entry(key) {
            Entry::Occupied(o) => *o.get(),
            Entry::Vacant(slot) => {
                let v = value::mk_pi(arena, domain, body);
                v.mark_canonical();
                *slot.insert(v)
            }
        }
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
