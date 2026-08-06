use crate::env::{Declar, RecursorData};
use crate::expr::{BinderStyle, Expr};
use crate::tc::{NatBinOp, TypeChecker};
use crate::util::{
    nat_div, nat_gcd, nat_land, nat_lor, nat_mod, nat_shl, nat_shr, nat_sub, nat_xor, BigUintPtr, ExprPtr, LevelPtr,
    LevelsPtr, NamePtr, StringPtr,
};
use crate::value::{self, Closure, Elim, ElimView, RigidHead, Spine, Value, E, S, V};
use num_bigint::BigUint;
use num_traits::pow::Pow;
use std::cell::OnceCell;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConstKind {
    Unfoldable,
    Ctor,
    Recursor,
    Quot,
    Inductive,
    Axiom,
}

enum ForceStep<'a> {
    Reduced(V<'a>),
    Descend(V<'a>),
    Done,
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
        self.tc_cache.bvar_hc.insert(key, v);
        v
    }

    fn mk_unfold_hc(
        &mut self,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
        spine: S<'t>,
        head_value: &'t OnceCell<V<'t>>,
    ) -> V<'t> {
        let key = (head_value as *const OnceCell<V<'t>> as usize, spine as *const Spine<'t> as usize);
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

    fn intern_frame(
        &mut self,
        hash: u64,
        mask: u64,
        slots: &[V<'t>],
        lsub: Option<&'t value::LevelSub<'t>>,
    ) -> E<'t> {
        let lsub_addr = lsub.map_or(0, |l| l as *const value::LevelSub<'t> as usize);
        if let Some(e) = self.tc_cache.frames.find(hash, |e: &E<'t>| match e {
            value::Env::Framed { mask: m, slots: sl, lsub: l, .. } =>
                *m == mask
                    && l.map_or(0, |l| l as *const value::LevelSub<'t> as usize) == lsub_addr
                    && sl.len() == slots.len()
                    && sl.iter().zip(slots).all(|(a, b)| std::ptr::eq(*a, *b)),
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
        self.tc_cache.frames.insert_unique(hash, e, |e| e.get_hash());
        e
    }

    fn lsub_base(&mut self, lsub: Option<&'t value::LevelSub<'t>>) -> E<'t> {
        let Some(ls) = lsub else { return self.tc_cache.empty_env };
        let key = ls as *const value::LevelSub<'t> as usize;
        if let Some(e) = self.tc_cache.lsub_bases.get(&key) {
            return e;
        }
        let e: E<'t> = self.arena.alloc(value::Env::Nil { lsub, hash: key as u64 });
        self.tc_cache.lsub_bases.insert(key, e);
        e
    }

    fn intern_level_sub(&mut self, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> &'t value::LevelSub<'t> {
        if let Some(l) = self.tc_cache.level_subs.get(&(ks, vs)) {
            return l;
        }
        let l: &'t value::LevelSub<'t> = self.arena.alloc(value::LevelSub { ks, vs });
        self.tc_cache.level_subs.insert((ks, vs), l);
        l
    }

    pub(crate) fn eval_inst(&mut self, ex: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> V<'t> {
        debug_assert_eq!(self.ctx.read_levels(ks).len(), self.ctx.read_levels(vs).len());
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
                    return e
                }
                let (m, r) = prune.get();
                if m == mask {
                    if let Some(r) = r {
                        return r;
                    }
                }
            }
            value::Env::Cons { prune, .. } => {
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
            >> crate::util::PRUNE_DM_SHIFT) as usize;
        let ent = self.tc_cache.prune_dm[slot];
        if ent.0 == e as *const value::Env<'t> as usize && ent.1 == mask {
            if let Some(hit) = ent.2 {
                match e {
                    value::Env::Cons { prune, .. } | value::Env::Framed { prune, .. } =>
                        prune.set((mask, Some(hit))),
                    value::Env::Nil { .. } => {}
                }
                return hit;
            }
        }
        self.prune_env_cold(e, mask, slot)
    }

    #[inline(never)]
    fn prune_env_cold(&mut self, e: E<'t>, mask: u64, slot: usize) -> E<'t> {
        let mut buf: [std::mem::MaybeUninit<V<'t>>; 64] = [const { std::mem::MaybeUninit::uninit() }; 64];
        let mut slots_hash = e.lsub().map_or(0, |l| l as *const value::LevelSub<'t> as usize as u64);
        let mut n = 0usize;
        let mut out_mask = 0u64;
        let mut rem = mask;
        let mut consumed = 0u32;
        let mut cur = e;
        while rem != 0 {
            match cur {
                value::Env::Nil { .. } => break,
                value::Env::Framed { mask: fmask, slots, .. } => {
                    let limit = 64 - consumed;
                    let bound = if limit >= 64 { u64::MAX } else { (1u64 << limit) - 1 };
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
        let slots: &[V<'t>] = unsafe { std::slice::from_raw_parts(buf.as_ptr().cast::<V<'t>>(), n) };
        let lsub = e.lsub();
        let hash = out_mask.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(slots_hash);
        let r = self.intern_frame(hash, out_mask, slots, lsub);
        self.tc_cache.prune_dm[slot] = (e as *const value::Env<'t> as usize, mask, Some(r));
        match e {
            value::Env::Cons { prune, .. } | value::Env::Framed { prune, .. } => prune.set((mask, Some(r))),
            value::Env::Nil { .. } => {}
        }
        r
    }

    #[inline]
    pub(crate) fn key_env(&mut self, env: E<'t>, e: ExprPtr<'t>) -> E<'t> {
        let k = e.num_loose_bvars();
        if k == 0 {
            return self.lsub_base(env.lsub());
        }
        if k > 64 {
            return env;
        }
        self.prune_env(env, e.as_ref().fv_mask())
    }

    pub(crate) fn mk_thunk_hc(&mut self, env: E<'t>, e: ExprPtr<'t>) -> V<'t> {
        let te = self.key_env(env, e);
        let key = (te as *const value::Env<'t> as usize, e);
        if let Some(v) = self.tc_cache.thunk_hc.get(&key) {
            return v;
        }
        let v = value::mk_thunk(self.arena, te, e);
        self.tc_cache.thunk_hc.insert(key, v);
        v
    }

    #[inline]
    fn spine_snoc_hc(&mut self, prev: S<'t>, elim: Elim<'t>) -> S<'t> {
        let key = (prev as *const Spine<'t> as usize, elim_key(&elim));
        if let Some(s) = self.tc_cache.spine_hc.get(&key) {
            return s;
        }
        let s = value::spine_snoc(self.arena, prev, elim);
        let canon = prev.is_canonical()
            && match elim.view() {
                ElimView::App(a) => a.is_canonical(),
                ElimView::Proj { .. } => true,
            };
        if canon {
            s.mark_canonical();
        }
        self.tc_cache.spine_hc.insert(key, s);
        s
    }

    #[inline]
    fn mk_rigid_hc(&mut self, head: RigidHead<'t>, spine: S<'t>) -> V<'t> {
        let hk = rigid_head_key(&head);
        let key = (hk.0, hk.1, hk.2, spine as *const Spine<'t> as usize);
        if let Some(v) = self.tc_cache.rigid_hc.get(&key) {
            return v;
        }
        let v = value::mk_rigid(self.arena, head, spine);
        if spine.is_canonical() {
            v.mark_canonical();
        }
        self.tc_cache.rigid_hc.insert(key, v);
        v
    }

    #[inline]
    fn mk_lam_hc(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: Closure<'t>,
    ) -> V<'t> {
        debug_assert!(body.ctx.is_none());
        let key = (binder_type, body.env as *const value::Env<'t> as usize, body.body);
        if let Some(v) = self.tc_cache.lam_hc.get(&key) {
            return v;
        }
        let v = value::mk_lam(self.arena, binder_name, binder_style, binder_type, body);
        v.mark_canonical();
        self.tc_cache.lam_hc.insert(key, v);
        v
    }

    #[inline]
    fn canonicalize_for_spine(&mut self, v: V<'t>) -> V<'t> {
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
            Value::Lam { binder_name, binder_style, binder_type, body, .. } =>
                self.mk_lam_hc(*binder_name, *binder_style, *binder_type, *body),
            Value::Pi { binder_name, binder_style, domain, body , ..} =>
                self.mk_pi_hc(*binder_name, *binder_style, domain, *body),
            Value::Sort { level , ..} => self.canon_content(0, level.get_hash(), v),
            Value::NatLit { ptr , ..} => self.canon_content(1, ptr.get_hash(), v),
            Value::StrLit { ptr , ..} => self.canon_content(2, ptr.get_hash(), v),
            Value::Rigid { head, spine , ..} => {
                let cspine = self.canon_spine(spine);
                self.mk_rigid_hc(*head, cspine)
            }
            Value::Unfold { head, spine, head_value, .. } => {
                let (hn, hl, hv, sp) = (head.name, head.levels, *head_value, *spine);
                let cspine = self.canon_spine(sp);
                self.mk_unfold_hc(hn, hl, cspine, hv)
            }
            Value::Thunk { .. } => v,
        }
    }

    #[inline]
    fn mk_pi_hc(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        domain: V<'t>,
        body: Closure<'t>,
    ) -> V<'t> {
        let key = (
            domain as *const Value<'t> as usize,
            body.env as *const value::Env<'t> as usize,
            body.body,
            body.ctx.map_or(0, |c| c as *const value::Ctx<'t> as usize),
        );
        if let Some(v) = self.tc_cache.pi_hc.get(&key) {
            return v;
        }
        let v = value::mk_pi(self.arena, binder_name, binder_style, domain, body);
        v.mark_canonical();
        self.tc_cache.pi_hc.insert(key, v);
        v
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "bmi2")]
unsafe fn pext(a: u64, m: u64) -> u64 { std::arch::x86_64::_pext_u64(a, m) }

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

#[inline]
fn mix(a: u128, b: u128) -> u128 {
    (a ^ b).wrapping_mul(0x9E37_79B9_7F4A_7C15_BF58_476D_1CE4_E5B9).rotate_left(47)
}

const WHNF_ADMIT_THRESHOLD: u8 = 2;

const FAIL_CLOSURE: u8 = 1;
const FAIL_DEPTH: u8 = 7;

impl<'x, 't, 'p> TypeChecker<'x, 't, 'p> {
    pub(crate) fn eval(&mut self, depth: u32, env: E<'t>, e: ExprPtr<'t>) -> V<'t> {
        if e.num_loose_bvars() == 0 && env.lsub().is_none() {
            if let Some(v) = self.tc_cache.closed_eval_cache.get(&e) {
                return v;
            }
            let v = self.eval_no_cache(depth, env, e);
            self.tc_cache.closed_eval_cache.insert(e, v);
            return v;
        }
        if matches!(
            self.ctx.read_expr_ref(e),
            Expr::App { .. } | Expr::Proj { .. } | Expr::Let { .. } | Expr::Pi { .. } | Expr::Lambda { .. }
        ) {
            let te = self.key_env(env, e);
            let key = (te as *const value::Env<'t> as usize, e);
            if let Some(v) = self.tc_cache.open_eval_cache.get(&key) {
                return v;
            }
            let v = self.eval_no_cache(depth, te, e);
            self.tc_cache.open_eval_cache.insert(key, v);
            return v;
        }
        self.eval_no_cache(depth, env, e)
    }

    fn eval_no_cache(&mut self, depth: u32, env: E<'t>, e: ExprPtr<'t>) -> V<'t> {
        let first = *self.ctx.read_expr_ref(e);
        if let Expr::App { fun, arg, .. } = first {
            if let &Expr::App { fun: f2, arg: a2, .. } = self.ctx.read_expr_ref(arg) {
                let first_fun = fun;
                let mut all_same = fun == f2;
                let mut count = 2u32;
                let mut cur = a2;
                let leaf_expr;
                loop {
                    match self.ctx.read_expr_ref(cur) {
                        &Expr::App { fun: fn3, arg: an3, .. } => {
                            count += 1;
                            if all_same && fn3 != first_fun {
                                all_same = false;
                            }
                            cur = an3;
                        }
                        _ => {
                            leaf_expr = cur;
                            break;
                        }
                    }
                }
                let mut result = self.eval(depth, env, leaf_expr);
                let nat_ext = self.nat_extension;

                if all_same {
                    let f_val = match self.ctx.read_expr_ref(first_fun) {
                        &Expr::Var { dbj_idx, .. } => {
                            let v = env.lookup(dbj_idx).expect("eval: loose bvar");
                            self.force_thunk(depth, v)
                        }
                        _ => self.eval(depth, env, first_fun),
                    };
                    if let Value::Rigid { head, spine , ..} = f_val {
                        let head_copy = *head;
                        let head_spine = *spine;
                        let is_nat_ctor = nat_ext && matches!(head_copy, RigidHead::Ctor(_, _));
                        if !is_nat_ctor {
                            for _ in 0..count {
                                let a = self.canonicalize_for_spine(result);
                                let ns = self.spine_snoc_hc(head_spine, Elim::app(a));
                                result = self.mk_rigid_hc(head_copy, ns);
                            }
                            return result;
                        }
                    }
                    for _ in 0..count {
                        result = self.apply(depth, f_val, result);
                    }
                    return result;
                }

                let mut funs: Vec<ExprPtr<'t>> = Vec::with_capacity(count as usize);
                funs.push(fun);
                funs.push(f2);
                let mut cur2 = a2;
                while let &Expr::App { fun: fn3, arg: an3, .. } = self.ctx.read_expr_ref(cur2) {
                    funs.push(fn3);
                    cur2 = an3;
                }
                let mut last_f_expr: Option<ExprPtr<'t>> = None;
                let mut last_f_val: Option<V<'t>> = None;
                while let Some(f_expr) = funs.pop() {
                    let f_val = if Some(f_expr) == last_f_expr {
                        last_f_val.unwrap()
                    } else {
                        let v = match self.ctx.read_expr_ref(f_expr) {
                            &Expr::Var { dbj_idx, .. } => {
                                let v = env.lookup(dbj_idx).expect("eval: loose bvar");
                                self.force_thunk(depth, v)
                            }
                            _ => self.eval(depth, env, f_expr),
                        };
                        last_f_expr = Some(f_expr);
                        last_f_val = Some(v);
                        v
                    };
                    if let Value::Rigid { head, spine , ..} = f_val {
                        let head_copy = *head;
                        let is_nat_ctor = nat_ext && matches!(head_copy, RigidHead::Ctor(_, _));
                        if !is_nat_ctor {
                            let sp = *spine;
                            let a = self.canonicalize_for_spine(result);
                            let ns = self.spine_snoc_hc(sp, Elim::app(a));
                            result = self.mk_rigid_hc(head_copy, ns);
                            continue;
                        }
                    }
                    result = self.apply(depth, f_val, result);
                }
                return result;
            }
            let f = self.eval(depth, env, fun);
            let trivial = matches!(
                self.ctx.read_expr_ref(arg),
                Expr::Var { .. }
                    | Expr::Sort { .. }
                    | Expr::Const { .. }
                    | Expr::NatLit { .. }
                    | Expr::StringLit { .. }
            );
            if let Value::Lam { body: clo, .. } = f {
                let a = if trivial { self.eval(depth, env, arg) } else { self.mk_thunk_hc(env, arg) };
                let clo_env = clo.env;
                let clo_body = clo.body;
                let new_env = value::env_extend(self.arena, clo_env, a);
                return self.eval(depth, new_env, clo_body);
            }
            let a = if trivial { self.eval(depth, env, arg) } else { self.mk_thunk_hc(env, arg) };
            return self.apply(depth, f, a);
        }
        match first {
            Expr::Var { dbj_idx, .. } => {
                let v = env.lookup(dbj_idx).expect("eval: loose bvar");
                self.force_thunk(depth, v)
            }
            Expr::Sort { level, .. } => {
                let level = match env.lsub() {
                    Some(ls) => self.ctx.subst_level(level, ls.ks, ls.vs),
                    None => level,
                };
                value::mk_sort(self.arena, self.ctx.simplify(level))
            }
            Expr::Const { name, levels, .. } => {
                let levels = match env.lsub() {
                    Some(ls) => self.ctx.subst_levels(levels, ls.ks, ls.vs),
                    None => levels,
                };
                self.eval_const(name, levels)
            }
            Expr::App { .. } => unreachable!(),
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } =>
                {
                let ce = self.key_env(env, e);
                value::mk_lam(self.arena, binder_name, binder_style, binder_type, Closure::mk_eval(ce, body))
            }
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                let dom = match self.ctx.read_expr_ref(binder_type) {
                    Expr::Var { .. }
                    | Expr::Sort { .. }
                    | Expr::Const { .. }
                    | Expr::NatLit { .. }
                    | Expr::StringLit { .. } => self.eval(depth, env, binder_type),
                    _ => self.mk_thunk_hc(env, binder_type),
                };
                {
                    let ce = self.key_env(env, e);
                    value::mk_pi(self.arena, binder_name, binder_style, dom, Closure::mk_eval(ce, body))
                }
            }
            Expr::Let { .. } => {
                let mut env = env;
                let mut cursor = e;
                while let Expr::Let { data: &crate::expr::LetData { val, body, .. }, .. } = self.ctx.read_expr(cursor) {
                    let vv = self.eval(depth, env, val);
                    env = value::env_extend(self.arena, env, vv);
                    cursor = body;
                }
                self.eval(depth, env, cursor)
            }
            Expr::Proj { ty_name, idx, structure, .. } => {
                let vs = self.eval(depth, env, structure);
                self.do_proj(depth, ty_name, idx, vs)
            }
            Expr::NatLit { ptr, .. } => value::mk_natlit(self.arena, ptr),
            Expr::StringLit { ptr, .. } => value::mk_strlit(self.arena, ptr),
        }
    }

    fn const_kind(&mut self, name: NamePtr<'t>) -> ConstKind {
        match self.env.get_declar(&name) {
            Some(Declar::Definition { .. }) | Some(Declar::Theorem { .. }) => ConstKind::Unfoldable,
            Some(Declar::Constructor(_)) => ConstKind::Ctor,
            Some(Declar::Recursor(_)) => ConstKind::Recursor,
            Some(Declar::Quot { .. }) => ConstKind::Quot,
            Some(Declar::Inductive(_)) => ConstKind::Inductive,
            Some(Declar::Axiom { .. }) | Some(Declar::Opaque { .. }) | None => ConstKind::Axiom,
        }
    }

    fn declar_val(&mut self, name: NamePtr<'t>) -> Option<(LevelsPtr<'t>, ExprPtr<'t>)> {
        self.env.get_declar_val(&name)
    }

    pub(crate) fn eval_const(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> V<'t> {
        if let Some(cached) = self.tc_cache.const_head_value_cache.get(&(name, levels)) {
            return cached;
        }
        let empty = self.empty_spine();
        let v = match self.const_kind(name) {
            ConstKind::Unfoldable => {
                let cell = &*self.arena.alloc(OnceCell::new());
                value::mk_unfold_head_with_empty(self.arena, name, levels, cell, empty)
            }
            ConstKind::Ctor =>
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Ctor(name, levels), empty),
            ConstKind::Recursor =>
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Recursor(name, levels), empty),
            ConstKind::Quot =>
                value::mk_rigid_head_with_empty(self.arena, RigidHead::QuotConst(name, levels), empty),
            ConstKind::Inductive =>
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Inductive(name, levels), empty),
            ConstKind::Axiom =>
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Axiom(name, levels), empty),
        };
        self.tc_cache.const_head_value_cache.insert((name, levels), v);
        v
    }

    pub(crate) fn const_result_level(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> Option<LevelPtr<'t>> {
        if let Some(cached) = self.tc_cache.const_result_level_cache.get(&(name, levels)).copied() {
            return Some(cached);
        }
        let head_ty = self.const_head_type(name, levels);
        let mut cur = head_ty;
        let mut binder_depth = 0u32;
        loop {
            let cur_f = self.force_all(binder_depth, cur);
            match cur_f {
                Value::Pi { domain, body, .. } => {
                    let fresh = self.mk_bvar_hc(binder_depth, domain);
                    cur = self.apply_closure(binder_depth + 1, body, fresh, Some(domain));
                    binder_depth += 1;
                }
                Value::Sort { level , ..} => {
                    let l = self.ctx.simplify(*level);
                    self.tc_cache.const_result_level_cache.insert((name, levels), l);
                    return Some(l);
                }
                _ => return None,
            }
        }
    }

    pub(crate) fn const_head_type(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> V<'t> {
        if let Some(cached) = self.tc_cache.const_head_type_cache.get(&(name, levels)) {
            return cached;
        }
        let info = match self.env.get_declar(&name) {
            Some(d) => *d.info(),
            None => panic!("const_head_type: unknown const {:?}", name),
        };
        let v = self.eval_inst(info.ty, info.uparams, levels);
        self.tc_cache.const_head_type_cache.insert((name, levels), v);
        v
    }

    #[inline]
    pub(crate) fn force_thunk(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        if let Value::Thunk { env, expr, forced , ..} = v {
            if let Some(r) = forced.get() {
                return r;
            }
            let r = self.eval(depth, env, *expr);
            let _ = forced.set(r);
            return r;
        }
        v
    }

    pub(crate) fn lam_domain(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        match v {
            Value::Lam { binder_type, body, .. } => {
                let addr = v as *const Value<'t> as usize;
                if let Some(d) = self.tc_cache.lam_domain_cache.get(&addr) {
                    return d;
                }
                let e = body.env;
                let bt = *binder_type;
                let d = self.eval(depth, e, bt);
                self.tc_cache.lam_domain_cache.insert(addr, d);
                d
            }
            Value::Pi { domain, .. } => domain,
            _ => panic!("lam_domain: not a Lam/Pi"),
        }
    }

    #[inline]
    pub(crate) fn apply(&mut self, depth: u32, f: V<'t>, a: V<'t>) -> V<'t> {
        match f {
            Value::Lam { body: clo, .. } => {
                let clo_env = clo.env;
                let clo_body = clo.body;
                let env = value::env_extend(self.arena, clo_env, a);
                self.eval(depth, env, clo_body)
            }
            Value::Rigid { head, spine , ..} => {
                let head_copy = *head;
                if self.nat_extension {
                    if let RigidHead::Ctor(name, _) = head_copy {
                        if Some(name) == self.ctx.export_file.name_cache.nat_succ {
                            let new_spine = value::spine_snoc(self.arena, spine, Elim::app(a));
                            return self.try_fire_rigid(depth, head_copy, new_spine);
                        }
                    }
                }
                let a = self.canonicalize_for_spine(a);
                let new_spine = self.spine_snoc_hc(spine, Elim::app(a));
                self.mk_rigid_hc(head_copy, new_spine)
            }
            Value::Unfold { head, spine, head_value, .. } => {
                let head = *head;
                let head_value = *head_value;
                let spine = *spine;
                if self.nat_extension && self.is_nat_red_name(head.name) {
                    let new_spine = self.spine_snoc_hc(spine, Elim::app(a));
                    if let Some(args) = self.spine_apps(depth, new_spine) {
                        if let Some(r) = self.do_nat_red_shallow(depth, head.name, &args) {
                            return r;
                        }
                    }
                    return self.mk_unfold_hc(head.name, head.levels, new_spine, head_value);
                }
                let a = self.canonicalize_for_spine(a);
                let new_spine = self.spine_snoc_hc(spine, Elim::app(a));
                self.mk_unfold_hc(head.name, head.levels, new_spine, head_value)
            }
            _ => panic!("apply: ill-typed application"),
        }
    }

    pub(crate) fn apply_v(&mut self, depth: u32, f: V<'t>, a: V<'t>) -> V<'t> { self.apply(depth, f, a) }

    pub(crate) fn apply_many(&mut self, depth: u32, f0: V<'t>, args: &[V<'t>]) -> V<'t> {
        let mut f = f0;
        let mut i = 0usize;
        while i < args.len() {
            let Value::Lam { body: clo, .. } = f else {
                f = self.apply(depth, f, args[i]);
                i += 1;
                continue
            };
            let mut env = value::env_extend(self.arena, clo.env, args[i]);
            let mut body = clo.body;
            i += 1;
            while i < args.len() {
                let Expr::Lambda { body: inner, .. } = self.ctx.read_expr(body) else { break };
                let pruned = self.key_env(env, body);
                env = value::env_extend(self.arena, pruned, args[i]);
                body = inner;
                i += 1;
            }
            f = self.eval(depth, env, body);
        }
        f
    }

    pub(crate) fn apply_closure(
        &mut self,
        depth: u32,
        clo: &Closure<'t>,
        v: V<'t>,
        binder_ty: Option<V<'t>>,
    ) -> V<'t> {
        let env = value::env_extend(self.arena, clo.env, v);
        match clo.ctx {
            None => self.eval(depth, env, clo.body),
            Some(clo_ctx) => {
                let ty = binder_ty.expect("apply_closure: infer closure without a binder type");
                let ctx = value::ctx_extend(self.arena, clo_ctx, ty);
                self.infer_value(crate::tc::InferFlag::InferOnly, depth, env, ctx, clo.body)
            }
        }
    }

    fn try_fire_rigid(&mut self, depth: u32, head: RigidHead<'t>, spine: S<'t>) -> V<'t> {
        if self.ctx.export_file.config.nat_extension {
            if let RigidHead::Ctor(name, _) = head {
                if Some(name) == self.ctx.export_file.name_cache.nat_succ {
                    if let Spine::Snoc { prev: Spine::Empty, elim, .. } = spine {
                        if let ElimView::App(arg) = elim.view() {
                            if let Some(n) = self.value_to_bignum_at(depth, arg, false) {
                                let succ_lit = n + 1u8;
                                if let Some(p) = self.ctx.alloc_bignum(succ_lit) {
                                    return value::mk_natlit(self.arena, p);
                                }
                            }
                        }
                    }
                }
            }
        }
        self.mk_rigid_hc(head, spine)
    }

    fn is_nat_red_name(&self, name: NamePtr<'t>) -> bool {
        let _nc = &self.ctx.export_file.name_cache;
        name.as_ref().is_nat_red()
    }

    fn nat_red_defer(&mut self, depth: u32, name: NamePtr<'t>, args: &[V<'t>]) -> bool {
        use crate::name::NatRed::*;
        let structural_on_second = matches!(name.as_ref().nat_red(), Some(Add | Sub | Mul | Pow));
        if !structural_on_second || args.len() != 2 {
            return false;
        }
        if let Value::NatLit { ptr , ..} = self.force_thunk(depth, args[1]) {
            self.ctx.read_bignum(*ptr).map(|n| n.bits() > 8).unwrap_or(false)
        } else {
            false
        }
    }

    pub(crate) fn value_type(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        let v = self.force_thunk(depth, v);
        match v {
            Value::Sort { level , ..} => {
                let s = self.ctx.succ(*level);
                value::mk_sort(self.arena, self.ctx.simplify(s))
            }
            Value::NatLit { .. } => {
                let n = self.ctx.export_file.name_cache.nat.expect("value_type: Nat name missing");
                let levels = self.ctx.alloc_levels_slice(&[]);
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Inductive(n, levels), self.empty_spine())
            }
            Value::StrLit { .. } => {
                let n = self.ctx.export_file.name_cache.string.expect("value_type: String name missing");
                let levels = self.ctx.alloc_levels_slice(&[]);
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Inductive(n, levels), self.empty_spine())
            }
            Value::Rigid { head, spine , ..} => {
                let head_ty = self.rigid_head_type(depth, *head);
                let prev = value::mk_rigid_head_with_empty(self.arena, *head, self.empty_spine());
                self.spine_type_with_value(depth, head_ty, prev, spine)
            }
            Value::Unfold { head, spine, .. } => {
                let head_ty = self.const_head_type(head.name, head.levels);
                let cell = &*self.arena.alloc(OnceCell::new());
                let _ = cell.set(head_ty);
                let prev =
                    value::mk_unfold_head_with_empty(self.arena, head.name, head.levels, cell, self.empty_spine());
                self.spine_type_with_value(depth, head_ty, prev, spine)
            }
            Value::Pi { .. } | Value::Lam { .. } => panic!("value_type: Pi/Lam not supported"),
            Value::Thunk { .. } => unreachable!("value_type: Thunk after force"),
        }
    }

    fn rigid_head_type(&mut self, _depth: u32, head: RigidHead<'t>) -> V<'t> {
        match head {
            RigidHead::BVar(_, ty) => ty,
            RigidHead::Axiom(n, ls)
            | RigidHead::Ctor(n, ls)
            | RigidHead::Recursor(n, ls)
            | RigidHead::QuotConst(n, ls)
            | RigidHead::Inductive(n, ls) => self.const_head_type(n, ls),
        }
    }

    fn spine_type_with_value(&mut self, depth: u32, mut ty: V<'t>, prev_head: V<'t>, spine: S<'t>) -> V<'t> {
        let mut prev = prev_head;
        for elim in spine.to_vec() {
            match elim.view() {
                ElimView::App(a) => {
                    let ty_f = self.force_all(depth, ty);
                    match ty_f {
                        Value::Pi { domain, body, .. } => {
                            ty = self.apply_closure(depth, body, a, Some(*domain));
                        }
                        _ => panic!("spine_type_with_value: expected Pi"),
                    }
                    prev = self.apply(depth, prev, a);
                }
                ElimView::Proj { ty_name, idx } => {
                    ty = self.proj_field_type_with(depth, prev, ty, ty_name, idx).expect("spine_type_with_value: bad proj");
                    prev = self.do_proj(depth, ty_name, idx, prev);
                }
            }
        }
        ty
    }

    pub(crate) fn whnf_head(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        if let Some(r) = self.store_lookup(depth, v) {
            return r;
        }
        let mut cur = v;
        let mut steps = 0u32;
        let result = loop {
            cur = self.force_thunk(depth, cur);
            match cur {
                Value::Unfold { .. } => {
                    let next = self.unfold_value(depth, cur);
                    if std::ptr::eq(next, cur) {
                        break cur;
                    }
                    steps += 1;
                    cur = next;
                }
                Value::Rigid { head: RigidHead::Recursor(..) | RigidHead::QuotConst(..), .. } =>
                    match self.iota_value(depth, cur) {
                        Some(next) => {
                            steps += 1;
                            cur = next;
                        }
                        None => break cur,
                    },
                _ => break cur,
            }
        };
        self.note_whnf(depth, v, result, steps);
        result
    }

    #[inline]
    fn note_whnf(&mut self, depth: u32, src: V<'t>, res: V<'t>, steps: u32) {
        if steps == 0 {
            return;
        }
        let closed = src.is_closed();
        let k = src.digest();
        if !closed {
            return;
        }
        let (fi, fb) = crate::util::tenure_slot(k as usize);
        if self.tc_cache.whnf_store_filter[fi] & fb != 0 && self.tc_cache.whnf_store.contains_key(&k) {
            return;
        }
        let ai = crate::util::admit_slot(k);
        let seen = &mut self.tc_cache.whnf_admit[ai];
        if *seen < WHNF_ADMIT_THRESHOLD {
            *seen = seen.saturating_add(1);
            return;
        }
        let Ok((full, verified)) = self.global_key(src, depth) else { return };
        if !verified {
            return;
        }
        let Some(hk) = Self::shallow_head_key(src) else { return };
        let q = self.quote(0, res);
        let (hi, hb) = crate::util::tenure_slot(hk as usize);
        self.tc_cache.whnf_head_filter[hi] |= hb;
        self.tc_cache.whnf_store_filter[fi] |= fb;
        self.tc_cache.whnf_store.insert(k, (full, q));
    }


    #[inline]
    fn shallow_head_key(v: V<'t>) -> Option<u64> {
        let (h, spine) = match v {
            Value::Unfold { head, spine, .. } =>
                (value::kmix(10, value::kmix(head.name.get_hash(), head.levels.get_hash())), *spine),
            Value::Rigid { head: RigidHead::Recursor(n, ls), spine, .. } =>
                (value::kmix(7, value::kmix(n.get_hash(), ls.get_hash())), *spine),
            Value::Rigid { head: RigidHead::QuotConst(n, ls), spine, .. } =>
                (value::kmix(8, value::kmix(n.get_hash(), ls.get_hash())), *spine),
            Value::Thunk { expr, .. } =>
                return Some(value::kmix(13, expr.as_ref() as *const Expr<'t> as usize as u64)),
            _ => return None,
        };
        Some(value::kmix(h, u64::from(spine.len())))
    }

    #[inline]
    fn store_lookup(&mut self, depth: u32, v: V<'t>) -> Option<V<'t>> {
        let hk = Self::shallow_head_key(v)?;
        let (hi, hb) = crate::util::tenure_slot(hk as usize);
        if self.tc_cache.whnf_head_filter[hi] & hb == 0 {
            return None;
        }
        if !v.is_closed() {
            return None;
        }
        let k = v.digest();
        let (fi, fb) = crate::util::tenure_slot(k as usize);
        if self.tc_cache.whnf_store_filter[fi] & fb == 0 {
            return None;
        }
        let &(full, e) = self.tc_cache.whnf_store.get(&k)?;
        let (mine, verified) = self.global_key(v, depth).ok()?;
        if !verified || mine != full {
            return None;
        }
        let env = self.empty_env();
        Some(self.eval(depth, env, e))
    }

    fn global_key(&mut self, v: V<'t>, depth: u32) -> Result<(u128, bool), u8> {
        let addr = v as *const Value<'t> as usize;
        if let Some(&k) = self.tc_cache.global_value_cache.get(&(addr, depth)) {
            return k;
        }
        let r = self.global_key_uncached(v, depth);
        self.tc_cache.global_value_cache.insert((addr, depth), r);
        r
    }

    fn global_key_uncached(&mut self, v: V<'t>, depth: u32) -> Result<(u128, bool), u8> {
        match v {
            Value::Sort { level , ..} => Ok((mix(1, u128::from(level.get_hash())), true)),
            Value::NatLit { ptr , ..} => Ok((mix(2, u128::from(ptr.get_hash())), true)),
            Value::StrLit { ptr , ..} => Ok((mix(3, u128::from(ptr.get_hash())), true)),
            Value::Rigid { head, spine , ..} => {
                let (h, c) = match *head {
                    RigidHead::BVar(lvl, ty) => {
                        if lvl >= depth {
                            return Err(FAIL_DEPTH);
                        }
                        let (t, _) = self.global_key(ty, depth)?;
                        (mix(mix(4, u128::from(depth - 1 - lvl)), t), false)
                    }
                    RigidHead::Axiom(n, ls) => (self.head_key(5, n, ls), true),
                    RigidHead::Ctor(n, ls) => (self.head_key(6, n, ls), true),
                    RigidHead::Recursor(n, ls) => (self.head_key(7, n, ls), true),
                    RigidHead::QuotConst(n, ls) => (self.head_key(8, n, ls), true),
                    RigidHead::Inductive(n, ls) => (self.head_key(9, n, ls), true),
                };
                self.spine_key(h, c, spine, depth)
            }
            Value::Unfold { head, spine, .. } => {
                let h = self.head_key(10, head.name, head.levels);
                self.spine_key(h, true, spine, depth)
            }
            Value::Lam { binder_name, binder_style, binder_type, body, .. } => {
                let h = self.binder_key(11, *binder_name, *binder_style, Some(*binder_type));
                self.closure_key(h, body, depth)
            }
            Value::Pi { binder_name, binder_style, domain, body , ..} => {
                let h = self.binder_key(12, *binder_name, *binder_style, None);
                let (d, dc) = self.global_key(domain, depth)?;
                let (k, cc) = self.closure_key(mix(h, d), body, depth)?;
                Ok((k, dc && cc))
            }
            Value::Thunk { env, expr, .. } => {
                let acc = mix(13, expr.as_ref() as *const Expr<'t> as usize as u128);
                self.env_key(acc, true, env, depth, expr.num_loose_bvars())
            }
        }
    }

    fn binder_key(
        &mut self,
        tag: u128,
        n: NamePtr<'t>,
        style: crate::expr::BinderStyle,
        ty: Option<ExprPtr<'t>>,
    ) -> u128 {
        let mut acc = mix(mix(tag, u128::from(n.get_hash())), style as u128);
        if let Some(t) = ty {
            acc = mix(acc, t.as_ref() as *const Expr<'t> as usize as u128);
        }
        acc
    }

    fn closure_key(&mut self, tag: u128, clo: &Closure<'t>, depth: u32) -> Result<(u128, bool), u8> {
        if clo.ctx.is_some() {
            return Err(FAIL_CLOSURE);
        }
        let acc = mix(tag, clo.body.as_ref() as *const Expr<'t> as usize as u128);
        self.env_key(acc, true, clo.env, depth, clo.body.num_loose_bvars().saturating_sub(1))
    }

    fn env_key(&mut self, acc: u128, closed: bool, env: E<'t>, depth: u32, count: u16) -> Result<(u128, bool), u8> {
        let mut acc = acc;
        let mut closed = closed;
        if let Some(ls) = env.lsub() {
            acc = mix(mix(acc, u128::from(ls.ks.get_hash())), u128::from(ls.vs.get_hash()));
        }
        for i in 0..count {
            if let Some(slot) = env.lookup(i) {
                let (k, c) = self.global_key(slot, depth)?;
                acc = mix(mix(acc, u128::from(i)), k);
                closed &= c;
            }
        }
        Ok((acc, closed))
    }

    fn head_key(&mut self, tag: u128, n: NamePtr<'t>, ls: LevelsPtr<'t>) -> u128 {
        mix(mix(tag, u128::from(n.get_hash())), u128::from(ls.get_hash()))
    }

    fn spine_key(&mut self, head: u128, closed: bool, s: S<'t>, depth: u32) -> Result<(u128, bool), u8> {
        let mut acc = head;
        let mut closed = closed;
        for elim in s.to_vec() {
            acc = match elim.view() {
                ElimView::App(a) => {
                    let (k, c) = self.global_key(a, depth)?;
                    closed &= c;
                    mix(acc, k)
                }
                ElimView::Proj { ty_name, idx } =>
                    mix(mix(acc, u128::from(ty_name.get_hash())), u128::from(idx) | (1 << 60)),
            };
        }
        Ok((acc, closed))
    }

    pub(crate) fn ctor_shape(&mut self, name: NamePtr<'t>) -> Option<(u16, u16, NamePtr<'t>)> {
        self.env.get_constructor(&name).map(|c| (c.num_params, c.num_fields, c.inductive_name))
    }

    pub(crate) fn can_be_struct_memo(&mut self, name: NamePtr<'t>) -> bool { self.env.can_be_struct(&name) }

    pub(crate) fn do_proj(&mut self, depth: u32, ty_name: NamePtr<'t>, idx: u16, v: V<'t>) -> V<'t> {
        let v = self.whnf_head(depth, v);
        match v {
            Value::Rigid { head: RigidHead::Ctor(ctor_name, _), spine, .. } => {
                if let Some((num_params, _, inductive_name)) = self.ctor_shape(*ctor_name) {
                    if inductive_name == ty_name {
                        let np = usize::from(num_params);
                        if let Some(ElimView::App(field)) = spine.get(np + usize::from(idx)).map(|e| e.view()) {
                            return self.force_thunk(depth, field);
                        }
                    }
                }
                self.proj_extend_spine(ty_name, idx, v)
            }
            Value::NatLit { ptr , ..} => {
                let ctor = self.nat_lit_to_ctor_val(depth, *ptr).expect("do_proj: nat_lit_to_ctor_val failed");
                self.do_proj(depth, ty_name, idx, ctor)
            }
            Value::StrLit { ptr , ..} => {
                let ctor = self.str_lit_to_ctor_val(depth, *ptr).expect("do_proj: str_lit_to_ctor_val failed");
                self.do_proj(depth, ty_name, idx, ctor)
            }
            Value::Rigid { .. } | Value::Unfold { .. } => self.proj_extend_spine(ty_name, idx, v),
            Value::Thunk { .. } => unreachable!("do_proj: Thunk after force_all"),
            _ => panic!("do_proj: not a neutral"),
        }
    }

    fn proj_extend_spine(&mut self, ty_name: NamePtr<'t>, idx: u16, v: V<'t>) -> V<'t> {
        match v {
            Value::Rigid { head, spine , ..} => {
                let (h, sp) = (*head, *spine);
                let ns = self.spine_snoc_hc(sp, Elim::proj(ty_name, idx));
                self.mk_rigid_hc(h, ns)
            }
            Value::Unfold { head, spine, head_value, .. } => {
                let (hn, hl, hv, sp) = (head.name, head.levels, *head_value, *spine);
                let ns = self.spine_snoc_hc(sp, Elim::proj(ty_name, idx));
                self.mk_unfold_hc(hn, hl, ns, hv)
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn proj_field_type_with(
        &mut self, depth: u32,
        struct_value: V<'t>,
        struct_ty: V<'t>,
        ty_name: NamePtr<'t>,
        idx: u16,
    ) -> Option<V<'t>> {
        let struct_ty = self.force_all(depth, struct_ty);
        let (ind_name, ind_levels, args) = match struct_ty {
            Value::Rigid { head: RigidHead::Inductive(n, ls), spine, .. } => {
                let aa = self.spine_apps(depth, spine)?;
                (*n, *ls, aa)
            }
            _ => return None,
        };
        if ind_name != ty_name {
            return None;
        }
        let ind = self.env.get_structure(&ind_name, true)?;
        let ctor_name = ind.all_ctor_names[0];
        let ctor_info = match self.env.get_declar(&ctor_name)? {
            Declar::Constructor(c) => c.info,
            _ => return None,
        };
        let mut cur = self.eval_inst(ctor_info.ty, ctor_info.uparams, ind_levels);
        let num_params = usize::from(ind.num_params);
        for i in 0..num_params {
            let cf = self.force_all(depth, cur);
            match cf {
                Value::Pi { domain, body, .. } => {
                    let arg = *args.get(i)?;
                    cur = self.apply_closure(depth, body, arg, Some(*domain));
                }
                _ => return None,
            }
        }
        for i in 0..idx {
            let cf = self.force_all(depth, cur);
            match cf {
                Value::Pi { domain, body, .. } => {
                    let prior = self.do_proj(depth, ty_name, i, struct_value);
                    cur = self.apply_closure(depth, body, prior, Some(*domain));
                }
                _ => return None,
            }
        }
        let cf = self.force_all(depth, cur);
        match cf {
            Value::Pi { domain, .. } => Some(*domain),
            _ => None,
        }
    }

    pub(crate) fn force_all(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        if let Some(r) = self.store_lookup(depth, v) {
            return r;
        }
        let mut cur = v;
        let mut steps = 0u32;
        let mut waiting: Vec<V<'t>> = Vec::new();
        let result = 'done: loop {
            loop {
                match cur {
                    Value::Thunk { .. } => cur = self.force_thunk(depth, cur),
                    Value::Unfold { .. } => {
                        let next = self.unfold_value(depth, cur);
                        if std::ptr::eq(next, cur) {
                            break;
                        }
                        steps += 1;
                        cur = next;
                    }
                    _ => break,
                }
            }
            let step = match cur {
                Value::Rigid { head: RigidHead::Recursor(..) | RigidHead::QuotConst(..), .. } => self.iota_step(depth, cur),
                _ => ForceStep::Done,
            };
            match step {
                ForceStep::Reduced(next) => {
                    steps += 1;
                    cur = next;
                    continue;
                }
                ForceStep::Descend(major) => {
                    waiting.push(cur);
                    cur = major;
                    continue;
                }
                ForceStep::Done => {}
            }
            loop {
                match waiting.pop() {
                    None => break 'done cur,
                    Some(rec_val) => {
                        let key = rec_val as *const Value<'t> as usize;
                        match self.fire_value(depth, rec_val, cur) {
                            Some(res) => {
                                self.tc_cache.iota_cache.insert(key, res);
                                steps += 1;
                                cur = res;
                                break;
                            }
                            None => {
                                self.tc_cache.iota_stuck.insert(key);
                                cur = rec_val;
                            }
                        }
                    }
                }
            }
        };
        self.note_whnf(depth, v, result, steps);
        result
    }

    fn iota_step(&mut self, depth: u32, v: V<'t>) -> ForceStep<'t> {
        let key = v as *const Value<'t> as usize;
        if self.tc_cache.iota_stuck.contains(&key) {
            return ForceStep::Done;
        }
        if let Some(c) = self.tc_cache.iota_cache.get(&key) {
            return ForceStep::Reduced(c);
        }
        match v {
            Value::Rigid { head: RigidHead::Recursor(name, levels), spine , ..} => {
                let env = self.env;
                let rec = match env.get_recursor(name) {
                    Some(r) => r,
                    None => return ForceStep::Done,
                };
                let args = match self.spine_apps(depth, spine) {
                    Some(a) => a,
                    None => return ForceStep::Done,
                };
                if args.len() <= rec.major_idx() {
                    return ForceStep::Done;
                }
                if let Some(r) = self.k_pre_reduce(depth, &rec, *levels, &args) {
                    self.tc_cache.iota_cache.insert(key, r);
                    return ForceStep::Reduced(r);
                }
                let major_h = self.strip_head(depth, args[rec.major_idx()]);
                if self.is_iota_reducible(major_h) {
                    return ForceStep::Descend(major_h);
                }
                match self.fire_recursor(depth, &rec, *levels, &args, major_h) {
                    Some(res) => {
                        self.tc_cache.iota_cache.insert(key, res);
                        ForceStep::Reduced(res)
                    }
                    None => {
                        self.tc_cache.iota_stuck.insert(key);
                        ForceStep::Done
                    }
                }
            }
            Value::Rigid { head: RigidHead::QuotConst(name, _), spine , ..} => {
                let cache = self.ctx.export_file.name_cache;
                let qmk_pos = if Some(*name) == cache.quot_lift {
                    5
                } else if Some(*name) == cache.quot_ind {
                    4
                } else {
                    return ForceStep::Done;
                };
                let name = *name;
                let args = match self.spine_apps(depth, spine) {
                    Some(a) => a,
                    None => return ForceStep::Done,
                };
                let major = match args.get(qmk_pos) {
                    Some(m) => *m,
                    None => return ForceStep::Done,
                };
                let major_h = self.strip_head(depth, major);
                if self.is_iota_reducible(major_h) {
                    return ForceStep::Descend(major_h);
                }
                match self.fire_quot(depth, name, &args, major_h) {
                    Some(res) => {
                        self.tc_cache.iota_cache.insert(key, res);
                        ForceStep::Reduced(res)
                    }
                    None => {
                        self.tc_cache.iota_stuck.insert(key);
                        ForceStep::Done
                    }
                }
            }
            _ => ForceStep::Done,
        }
    }

    fn strip_head(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        let mut cur = v;
        loop {
            match cur {
                Value::Thunk { .. } => cur = self.force_thunk(depth, cur),
                Value::Unfold { .. } => {
                    let next = self.unfold_value(depth, cur);
                    if std::ptr::eq(next, cur) {
                        return cur;
                    }
                    cur = next;
                }
                _ => return cur,
            }
        }
    }

    fn is_iota_reducible(&self, v: V<'t>) -> bool {
        match v {
            Value::Rigid { head: RigidHead::Recursor(..), .. } => true,
            Value::Rigid { head: RigidHead::QuotConst(name, _), .. } => {
                let cache = self.ctx.export_file.name_cache;
                Some(*name) == cache.quot_lift || Some(*name) == cache.quot_ind
            }
            _ => false,
        }
    }

    fn fire_value(&mut self, depth: u32, rec_val: V<'t>, major: V<'t>) -> Option<V<'t>> {
        match rec_val {
            Value::Rigid { head: RigidHead::Recursor(name, levels), spine , ..} => {
                let env = self.env;
                let rec = env.get_recursor(name)?;
                let args = self.spine_apps(depth, spine)?;
                if args.len() <= rec.major_idx() {
                    return None;
                }
                self.fire_recursor(depth, &rec, *levels, &args, major)
            }
            Value::Rigid { head: RigidHead::QuotConst(name, _), spine , ..} => {
                let args = self.spine_apps(depth, spine)?;
                self.fire_quot(depth, *name, &args, major)
            }
            _ => None,
        }
    }

    pub(crate) fn unfold_value(&mut self, depth: u32, v: V<'t>) -> V<'t> { self.unfold_value_go(depth, v, false) }

    pub(crate) fn unfold_value_demand(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        self.unfold_value_go(depth, v, self.tc_cache.probe_depth == 0)
    }

    fn unfold_value_go(&mut self, depth: u32, v: V<'t>, force: bool) -> V<'t> {
        if let Value::Unfold { head, spine, head_value, forced , ..} = v {
            if let Some(f) = forced.get() {
                return f;
            }
            if self.nat_extension && self.is_nat_red_name(head.name) {
                if let Some(args) = self.spine_apps(depth, spine) {
                    if let Some(r) = self.do_nat_red(depth, head.name, &args) {
                        let _ = forced.set(r);
                        return r;
                    }
                    if !force && self.nat_red_defer(depth, head.name, &args) {
                        return v;
                    }
                }
            }
            let head_value = match head_value.get() {
                Some(hv) => *hv,
                None => match self.unfold_const(head.name, head.levels) {
                    Some(hv) => {
                        let _ = head_value.set(hv);
                        hv
                    }
                    None => {
                        let _ = forced.set(v);
                        return v;
                    }
                },
            };
            let spine = *spine;
            let mut cur = head_value;
            let mut run: Vec<V<'t>> = Vec::new();
            for e in spine.to_vec() {
                match e.view() {
                    ElimView::App(a) => run.push(a),
                    ElimView::Proj { ty_name, idx } => {
                        if !run.is_empty() {
                            cur = self.apply_many(depth, cur, &run);
                            run.clear();
                        }
                        cur = self.do_proj(depth, ty_name, idx, cur);
                    }
                }
            }
            if !run.is_empty() {
                cur = self.apply_many(depth, cur, &run);
            }
            let _ = forced.set(cur);
            return cur;
        }
        v
    }

    pub(crate) fn iota_value(&mut self, depth: u32, v: V<'t>) -> Option<V<'t>> {
        let v_key = v as *const Value<'t> as usize;
        if self.tc_cache.iota_stuck.contains(&v_key) {
            return None;
        }
        if let Some(cached) = self.tc_cache.iota_cache.get(&v_key) {
            return Some(*cached);
        }
        let result = match v {
            Value::Rigid { head: RigidHead::Recursor(name, levels), spine, .. } => {
                let args = self.spine_apps(depth, spine)?;
                self.do_recursor_iota(depth, *name, *levels, &args)
            }
            Value::Rigid { head: RigidHead::QuotConst(name, _), spine, .. } => {
                let args = self.spine_apps(depth, spine)?;
                self.do_quot_iota(depth, *name, &args)
            }
            _ => None,
        };
        match result {
            None => {
                self.tc_cache.iota_stuck.insert(v_key);
            }
            Some(r) => {
                self.tc_cache.iota_cache.insert(v_key, r);
            }
        }
        result
    }

    pub(crate) fn unfold_const(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> Option<V<'t>> {
        if let Some(cached) = self.tc_cache.unfold_const_cache.get(&(name, levels)) {
            return Some(*cached);
        }
        let (def_uparams, def_value) = self.declar_val(name)?;
        if self.ctx.read_levels(levels).len() != self.ctx.read_levels(def_uparams).len() {
            return None;
        }
        let v = self.eval_inst(def_value, def_uparams, levels);
        self.tc_cache.unfold_const_cache.insert((name, levels), v);
        Some(v)
    }

    pub(crate) fn spine_apps(&mut self, depth: u32, spine: S<'t>) -> Option<Vec<V<'t>>> {
        let mut out = Vec::with_capacity(spine.len() as usize);
        let mut cur: &Spine<'t> = spine;
        while let Spine::Snoc { prev, elim, .. } = cur {
            match elim.view() {
                ElimView::App(a) => out.push(self.force_thunk(depth, a)),
                ElimView::Proj { .. } => return None,
            }
            cur = prev;
        }
        out.reverse();
        Some(out)
    }

    fn do_recursor_iota(&mut self, depth: u32, name: NamePtr<'t>, levels: LevelsPtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        let env = self.env;
        let rec = env.get_recursor(&name)?;
        if args.len() <= rec.major_idx() {
            return None;
        }
        if let Some(r) = self.k_pre_reduce(depth, &rec, levels, args) {
            return Some(r);
        }
        let major = self.whnf_head(depth, args[rec.major_idx()]);
        self.fire_recursor(depth, &rec, levels, args, major)
    }

    fn k_pre_reduce(&mut self, depth: u32, rec: &RecursorData<'t>, levels: LevelsPtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        if !rec.is_k {
            return None;
        }
        let raw = self.force_thunk(depth, args[rec.major_idx()]);
        let kctor = self.try_k_reduce(depth, raw, rec)?;
        self.fire_recursor(depth, rec, levels, args, kctor)
    }

    fn fire_recursor(
        &mut self, depth: u32,
        rec: &RecursorData<'t>,
        levels: LevelsPtr<'t>,
        args: &[V<'t>],
        major: V<'t>,
    ) -> Option<V<'t>> {
        if self.ctx.export_file.config.nat_extension
            && rec.all_inductives.first().copied() == self.ctx.export_file.name_cache.nat
        {
            if let Value::NatLit { ptr , ..} = major {
                return Some(self.nat_rec_natlit(depth, args, *ptr, rec, levels));
            }
        }
        let major = self
            .major_to_ctor(depth, major)
            .or_else(|| self.try_k_reduce(depth, major, rec))
            .or_else(|| self.try_struct_eta_reduce(depth, major, rec))
            .unwrap_or(major);
        let (ctor_name, ctor_args) = self.unwrap_ctor_app(depth, major)?;
        let rec_rule = rec.rec_rules.iter().find(|r| r.ctor_name == ctor_name).copied()?;
        let num_extra = ctor_args.len().checked_sub(usize::from(rec_rule.ctor_telescope_size_wo_params))?;
        let cache_key = (rec_rule.val, levels);
        let mut result = match self.tc_cache.rec_rule_cache.get(&cache_key) {
            Some(v) => *v,
            None => {
                let v = self.eval_inst(rec_rule.val, rec.info.uparams, levels);
                self.tc_cache.rec_rule_cache.insert(cache_key, v);
                v
            }
        };
        let nprefix = usize::from(rec.num_params + rec.num_motives + rec.num_minors);
        result = self.apply_many(depth, result, &args[..nprefix]);
        result = self.apply_many(depth, result, &ctor_args[num_extra..]);
        result = self.apply_many(depth, result, &args[rec.major_idx() + 1..]);
        Some(result)
    }

    fn nat_rec_natlit(
        &mut self, depth: u32,
        args: &[V<'t>],
        n_ptr: BigUintPtr<'t>,
        rec: &RecursorData<'t>,
        levels: LevelsPtr<'t>,
    ) -> V<'t> {
        use num_traits::Zero;
        let n = self.ctx.read_bignum(n_ptr).expect("nat_rec_natlit: NatLit ptr").clone();
        let nparams = usize::from(rec.num_params);
        let nmotives = usize::from(rec.num_motives);
        let major_idx = rec.major_idx();
        let zero_case = args[nparams + nmotives];
        let succ_case = self.force_thunk(depth, args[nparams + nmotives + 1]);
        let result = if n.is_zero() {
            zero_case
        } else {
            let pred = n - 1u8;
            let pred_ptr = self.ctx.alloc_bignum(pred).expect("nat_rec_natlit: alloc pred");
            let pred_val = value::mk_natlit(self.arena, pred_ptr);
            let empty = self.empty_spine();
            let mut ih = value::mk_rigid_head_with_empty(self.arena, RigidHead::Recursor(rec.info.name, levels), empty);
            for a in &args[..major_idx] {
                ih = self.apply_v(depth, ih, a);
            }
            ih = self.apply_v(depth, ih, pred_val);
            let stepped = self.apply_v(depth, succ_case, pred_val);
            self.apply_v(depth, stepped, ih)
        };
        self.apply_many(depth, result, &args[major_idx + 1..])
    }

    fn try_struct_eta_reduce(&mut self, depth: u32, major: V<'t>, rec: &RecursorData<'t>) -> Option<V<'t>> {
        if !matches!(major, Value::Rigid { .. } | Value::Unfold { .. }) {
            return None;
        }
        let rec_induct = self.ctx.get_major_induct(rec)?;
        if !self.can_be_struct_memo(rec_induct) {
            return None;
        }
        let key = (major as *const Value<'t> as usize, rec_induct);
        if let Some(cached) = self.tc_cache.struct_eta_cache.get(&key) {
            return *cached;
        }
        let result = self.try_struct_eta_reduce_uncached(depth, major, rec, rec_induct);
        self.tc_cache.struct_eta_cache.insert(key, result);
        result
    }

    fn try_struct_eta_reduce_uncached(
        &mut self, depth: u32,
        major: V<'t>,
        rec: &RecursorData<'t>,
        rec_induct: NamePtr<'t>,
    ) -> Option<V<'t>> {
        let major_ty = self.value_type(depth, major);
        let major_ty_f = self.force_all(depth, major_ty);
        let (ty_name, ty_levels, ty_args) = self.unwrap_inductive_app(depth, major_ty_f)?;
        if ty_name != rec_induct {
            return None;
        }
        let ind = self.env.get_inductive(&ty_name)?;
        let ctor_name = ind.all_ctor_names[0];
        let ctor_data = self.env.get_constructor(&ctor_name)?;
        let num_fields = ctor_data.num_fields;
        let np = usize::from(rec.num_params);
        let mut new_ctor =
            value::mk_rigid_head_with_empty(self.arena, RigidHead::Ctor(ctor_name, ty_levels), self.empty_spine());
        for a in ty_args.iter().take(np).copied() {
            new_ctor = self.apply_v(depth, new_ctor, a);
        }
        for i in 0..num_fields {
            let proj = self.do_proj(depth, ty_name, i, major);
            new_ctor = self.apply_v(depth, new_ctor, proj);
        }
        Some(new_ctor)
    }

    fn try_k_reduce(&mut self, depth: u32, major: V<'t>, rec: &RecursorData<'t>) -> Option<V<'t>> {
        if !rec.is_k {
            return None;
        }
        if !matches!(major, Value::Rigid { .. } | Value::Unfold { .. }) {
            return None;
        }
        let major_ty = self.value_type(depth, major);
        let major_ty_f = self.force_all(depth, major_ty);
        let (ty_name, ty_levels, ty_args) = self.unwrap_inductive_app(depth, major_ty_f)?;
        let rec_induct = self.ctx.get_major_induct(rec)?;
        if ty_name != rec_induct {
            return None;
        }
        let ind = self.env.get_inductive(&ty_name)?;
        let ctor_name = ind.all_ctor_names[0];
        let np = usize::from(rec.num_params);
        let ctor_self = rec
            .rec_rules
            .iter()
            .find(|r| r.ctor_name == ctor_name)
            .map(|r| usize::from(r.ctor_telescope_size_wo_params))
            .unwrap_or(0);
        let take = (np + ctor_self).min(ty_args.len());
        let mut new_ctor =
            value::mk_rigid_head_with_empty(self.arena, RigidHead::Ctor(ctor_name, ty_levels), self.empty_spine());
        for a in ty_args.iter().take(take).copied() {
            new_ctor = self.apply_v(depth, new_ctor, a);
        }
        let new_ty = self.value_type(depth, new_ctor);
        if !self.conv_types_at(depth, major_ty_f, new_ty) {
            return None;
        }
        Some(new_ctor)
    }

    fn unwrap_inductive_app(&mut self, depth: u32, v: V<'t>) -> Option<(NamePtr<'t>, LevelsPtr<'t>, Vec<V<'t>>)> {
        match v {
            Value::Rigid { head: RigidHead::Inductive(n, ls), spine, .. } => {
                let args = self.spine_apps(depth, spine)?;
                Some((*n, *ls, args))
            }
            _ => None,
        }
    }

    fn major_to_ctor(&mut self, depth: u32, major: V<'t>) -> Option<V<'t>> {
        match major {
            Value::NatLit { ptr , ..} => self.nat_lit_to_ctor_val(depth, *ptr),
            Value::StrLit { ptr , ..} => self.str_lit_to_ctor_val(depth, *ptr),
            _ => None,
        }
    }

    pub(crate) fn str_lit_to_ctor_val(&mut self, depth: u32, s: StringPtr<'t>) -> Option<V<'t>> {
        let ctor_expr = self.ctx.str_lit_to_constructor(s)?;
        let empty = self.empty_env();
        let v = self.eval(depth, empty, ctor_expr);
        Some(self.whnf_head(depth, v))
    }

    fn nat_lit_to_ctor_val(&mut self, depth: u32, n: BigUintPtr<'t>) -> Option<V<'t>> {
        if !self.ctx.export_file.config.nat_extension {
            return None;
        }
        use num_traits::Zero;
        let nv = self.ctx.read_bignum(n)?.clone();
        let levels = self.ctx.alloc_levels_slice(&[]);
        let empty = self.empty_spine();
        if nv.is_zero() {
            let zero_name = self.ctx.export_file.name_cache.nat_zero?;
            Some(value::mk_rigid_head_with_empty(self.arena, RigidHead::Ctor(zero_name, levels), empty))
        } else {
            let pred = self.ctx.alloc_bignum(core::ops::Sub::sub(nv, 1u8))?;
            let pred_v = value::mk_natlit(self.arena, pred);
            let succ_name = self.ctx.export_file.name_cache.nat_succ?;
            let succ_v = value::mk_rigid_head_with_empty(self.arena, RigidHead::Ctor(succ_name, levels), empty);
            Some(self.apply_v(depth, succ_v, pred_v))
        }
    }

    fn unwrap_ctor_app(&mut self, depth: u32, v: V<'t>) -> Option<(NamePtr<'t>, Vec<V<'t>>)> {
        match v {
            Value::Rigid { head: RigidHead::Ctor(name, _), spine, .. } => {
                let args = self.spine_apps(depth, spine)?;
                Some((*name, args))
            }
            _ => None,
        }
    }

    fn do_quot_iota(&mut self, depth: u32, c_name: NamePtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        let cache = self.ctx.export_file.name_cache;
        let qmk_pos = if Some(c_name) == cache.quot_lift {
            5usize
        } else if Some(c_name) == cache.quot_ind {
            4usize
        } else {
            return None;
        };
        let qmk = self.force_all(depth, *args.get(qmk_pos)?);
        self.fire_quot(depth, c_name, args, qmk)
    }

    fn fire_quot(&mut self, depth: u32, c_name: NamePtr<'t>, args: &[V<'t>], qmk: V<'t>) -> Option<V<'t>> {
        let cache = self.ctx.export_file.name_cache;
        let rest_idx = if Some(c_name) == cache.quot_lift {
            6usize
        } else if Some(c_name) == cache.quot_ind {
            5usize
        } else {
            return None;
        };
        let (qmk_head, qmk_spine) = match qmk {
            Value::Rigid { head: RigidHead::QuotConst(name, _), spine, .. } => (*name, *spine),
            _ => return None,
        };
        if Some(qmk_head) != cache.quot_mk {
            return None;
        }
        let qmk_args = self.spine_apps(depth, qmk_spine)?;
        if qmk_args.len() != 3 {
            return None;
        }
        let f = *args.get(3)?;
        let last = qmk_args[2];
        let result = self.apply_v(depth, f, last);
        Some(self.apply_many(depth, result, &args[rest_idx..]))
    }

    fn do_nat_red(&mut self, depth: u32, name: NamePtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        self.do_nat_red_at(depth, name, args, true)
    }

    fn do_nat_red_shallow(&mut self, depth: u32, name: NamePtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        self.do_nat_red_at(depth, name, args, false)
    }

    fn do_nat_red_at(&mut self, depth: u32, name: NamePtr<'t>, args: &[V<'t>], deep: bool) -> Option<V<'t>> {
        use crate::name::NatRed;
        let kind = name.as_ref().nat_red()?;
        if let NatRed::Succ = kind {
            if args.len() != 1 {
                return None;
            }
            let n = self.value_to_bignum_at(depth, args[0], deep)?;
            return self.mk_natlit_val(n + 1u8);
        }
        if let NatRed::DivGo | NatRed::ModCoreGo = kind {
            if args.len() != 5 {
                return None;
            }
            let y = self.value_to_bignum_at(depth, args[0], deep)?;
            let x = self.value_to_bignum_at(depth, args[3], deep)?;
            let op = if let NatRed::DivGo = kind { NatBinOp::Div } else { NatBinOp::Mod };
            return self.do_nat_bin_val(x, y, op);
        }
        if args.len() != 2 {
            return None;
        }
        let op = match kind {
            NatRed::Add => NatBinOp::Add,
            NatRed::Sub => NatBinOp::Sub,
            NatRed::Mul => NatBinOp::Mul,
            NatRed::Pow => NatBinOp::Pow,
            NatRed::Mod => NatBinOp::Mod,
            NatRed::Div => NatBinOp::Div,
            NatRed::Beq => NatBinOp::Beq,
            NatRed::Ble => NatBinOp::Ble,
            NatRed::LAnd => NatBinOp::LAnd,
            NatRed::LOr => NatBinOp::LOr,
            NatRed::XOr => NatBinOp::XOr,
            NatRed::Gcd => NatBinOp::Gcd,
            NatRed::Shl => NatBinOp::Shl,
            NatRed::Shr => NatBinOp::Shr,
            NatRed::Succ | NatRed::DivGo | NatRed::ModCoreGo => unreachable!(),
        };
        let xn = self.value_to_bignum_at(depth, args[0], deep)?;
        let yn = self.value_to_bignum_at(depth, args[1], deep)?;
        self.do_nat_bin_val(xn, yn, op)
    }

    fn do_nat_bin_val(&mut self, x: BigUint, y: BigUint, op: NatBinOp) -> Option<V<'t>> {
        use NatBinOp::*;
        match op {
            Add => self.mk_natlit_val(x + y),
            Sub => self.mk_natlit_val(nat_sub(x, y)),
            Mul => self.mk_natlit_val(x * y),
            Pow => self.mk_natlit_val(x.pow(y)),
            Div => self.mk_natlit_val(nat_div(x, y)),
            Mod => self.mk_natlit_val(nat_mod(x, y)),
            Gcd => self.mk_natlit_val(nat_gcd(&x, &y)),
            LAnd => self.mk_natlit_val(nat_land(x, y)),
            LOr => self.mk_natlit_val(nat_lor(x, y)),
            XOr => self.mk_natlit_val(nat_xor(&x, &y)),
            Shl => self.mk_natlit_val(nat_shl(x, y)),
            Shr => self.mk_natlit_val(nat_shr(x, y)),
            Beq => self.bool_val(x == y),
            Ble => self.bool_val(x <= y),
        }
    }

    fn mk_natlit_val(&mut self, n: BigUint) -> Option<V<'t>> {
        let p = self.ctx.alloc_bignum(n)?;
        Some(value::mk_natlit(self.arena, p))
    }

    fn bool_val(&mut self, b: bool) -> Option<V<'t>> {
        let cache = self.ctx.export_file.name_cache;
        let n = if b { cache.bool_true? } else { cache.bool_false? };
        let levels = self.ctx.alloc_levels_slice(&[]);
        Some(value::mk_rigid_head_with_empty(self.arena, RigidHead::Ctor(n, levels), self.empty_spine()))
    }

    pub(crate) fn value_has_free_bvar(&mut self, depth: u32, v: V<'t>) -> bool {
        let v = self.force_thunk(depth, v);
        let key = v as *const Value<'t> as usize;
        if let Some(&b) = self.tc_cache.fvar_cache.get(&key) {
            return b;
        }
        let r = match v {
            Value::Sort { .. } | Value::NatLit { .. } | Value::StrLit { .. } => false,
            Value::Rigid { head: RigidHead::BVar(..), .. } => true,
            Value::Rigid { spine, .. } | Value::Unfold { spine, .. } => {
                let mut found = false;
                let mut s = *spine;
                loop {
                    match s {
                        Spine::Empty => break,
                        Spine::Snoc { prev, elim, .. } => {
                            if let ElimView::App(a) = elim.view() {
                                if self.value_has_free_bvar(depth, a) {
                                    found = true;
                                    break;
                                }
                            }
                            s = *prev;
                        }
                    }
                }
                found
            }
            Value::Lam { .. } | Value::Pi { .. } => false,
            Value::Thunk { .. } => unreachable!("force_thunk left a Thunk"),
        };
        self.tc_cache.fvar_cache.insert(key, r);
        r
    }

    pub(crate) fn value_to_bignum(&mut self, depth: u32, v: V<'t>) -> Option<BigUint> { self.value_to_bignum_at(depth, v, true) }

    fn value_to_bignum_at(&mut self, depth: u32, v: V<'t>, deep: bool) -> Option<BigUint> {
        let mut succs: u64 = 0;
        let mut cur = self.force_thunk(depth, v);
        loop {
            match cur {
                Value::NatLit { ptr , ..} => {
                    return self.ctx.read_bignum(*ptr).cloned().map(|n| n + succs);
                }
                Value::Rigid { head: RigidHead::Ctor(name, _), spine, .. } => {
                    if Some(*name) == self.ctx.export_file.name_cache.nat_zero && spine.is_empty() {
                        return Some(BigUint::from(succs));
                    }
                    if Some(*name) == self.ctx.export_file.name_cache.nat_succ {
                        if let Spine::Snoc { prev: Spine::Empty, elim, .. } = spine {
                            if let ElimView::App(a) = elim.view() {
                                succs += 1;
                                cur = self.force_thunk(depth, a);
                                continue;
                            }
                        }
                    }
                    return None;
                }
                Value::Unfold { head_value, .. } => {
                    if let Some(Value::NatLit { ptr , ..}) = head_value.get() {
                        return self.ctx.read_bignum(*ptr).cloned().map(|n| n + succs);
                    }
                    if !deep {
                        return None;
                    }
                    return self.bignum_via_force(depth, cur).map(|n| n + succs);
                }
                Value::Rigid { head: RigidHead::Recursor(..) | RigidHead::QuotConst(..), .. } => {
                    if !deep {
                        return None;
                    }
                    return self.bignum_via_force(depth, cur).map(|n| n + succs);
                }
                _ => return None,
            }
        }
    }

    fn bignum_via_force(&mut self, depth: u32, v: V<'t>) -> Option<BigUint> {
        if self.value_has_free_bvar(depth, v) {
            return None;
        }
        let f = self.force_all(depth, v);
        match f {
            Value::NatLit { ptr , ..} => self.ctx.read_bignum(*ptr).cloned(),
            Value::Rigid { head: RigidHead::Ctor(name, _), .. }
                if Some(*name) == self.ctx.export_file.name_cache.nat_zero
                    || Some(*name) == self.ctx.export_file.name_cache.nat_succ =>
            {
                if std::ptr::eq(f, v) {
                    return None;
                }
                self.value_to_bignum(depth, f)
            }
            _ => None,
        }
    }
}
