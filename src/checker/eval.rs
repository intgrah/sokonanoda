// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::memo;
use crate::checker::env::Declar;
use crate::checker::tc::TypeChecker;
use crate::checker::value::{Closure, E, Elim, ElimView, RigidHead, S, Spine, V, Value};
use crate::outcome::{ensure, reject};
use crate::term::expr::{Expr, ExprNode, SPINE, SpineArgs};
use crate::term::id::{ExprId, LevelId, LevelsId, NameId};
use std::mem::MaybeUninit;

mod environment;
mod reduction;
mod whnf_cache;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstKind {
    Unfoldable,
    Ctor,
    Recursor,
    Quot,
    Inductive,
    Axiom,
}

impl TypeChecker<'_, '_> {
    #[inline(always)]
    pub(crate) fn eval(&mut self, depth: u32, env: E, e: ExprId) -> V {
        let node = *self.ctx.node(e);
        if let Expr::Var { dbj_idx } = node.expr {
            return self
                .vals()
                .env_lookup(env, dbj_idx)
                .expect("eval: loose bvar");
        }
        self.eval_node(depth, env, e, node)
    }

    fn eval_node(&mut self, depth: u32, env: E, e: ExprId, node: ExprNode) -> V {
        if node.loose == 0 {
            let Some(ls) = self.vals().env_lsub(env) else {
                return memo!(
                    self.tc_cache.closed_eval_cache,
                    e,
                    self.eval_no_cache(depth, env, e, node.expr)
                );
            };
            return memo!(self.tc_cache.closed_lsub_eval_cache, (e, ls), {
                let base = self.lsub_base(Some(ls));
                self.eval_no_cache(depth, base, e, node.expr)
            });
        }
        if matches!(
            node.expr,
            Expr::App { .. }
                | Expr::Proj { .. }
                | Expr::Let { .. }
                | Expr::Pi { .. }
                | Expr::Lambda { .. }
        ) {
            let te = self.prune_env(env, node.mask);
            return memo!(
                self.tc_cache.open_eval_cache,
                (te, e),
                self.eval_no_cache(depth, te, e, node.expr)
            );
        }
        self.eval_no_cache(depth, env, e, node.expr)
    }

    fn eval_no_cache(&mut self, depth: u32, env: E, e: ExprId, first: Expr) -> V {
        if let Expr::App { fun, arg } = first {
            if let Expr::App { fun: f2, arg: a2 } = self.ctx.ex(arg) {
                let first_fun = fun;
                let mut all_same = fun == f2;
                let mut count = 2u32;
                let mut cur = a2;
                let leaf_expr = loop {
                    match self.ctx.ex(cur) {
                        Expr::App { fun: fn3, arg: an3 } => {
                            count += 1;
                            if all_same && fn3 != first_fun {
                                all_same = false;
                            }
                            cur = an3;
                        }
                        _ => break cur,
                    }
                };
                let mut result = self.eval(depth, env, leaf_expr);

                if all_same {
                    let f_val = self.eval(depth, env, first_fun);
                    if self.vals().is_inert_rigid(f_val) {
                        for _ in 0..count {
                            result = self.neutral_app(f_val, result);
                        }
                        return result;
                    }
                    for _ in 0..count {
                        result = self.apply(depth, f_val, result);
                    }
                    return result;
                }

                let mut funs = SpineArgs::new();
                funs.push(fun);
                funs.push(f2);
                let mut cur2 = a2;
                while let Expr::App { fun: fn3, arg: an3 } = self.ctx.ex(cur2) {
                    funs.push(fn3);
                    cur2 = an3;
                }

                let mut last_f_expr: Option<ExprId> = None;
                let mut last_f_val: Option<V> = None;
                while let Some(f_expr) = funs.pop() {
                    let f_val = if Some(f_expr) == last_f_expr {
                        last_f_val.unwrap()
                    } else {
                        let v = self.eval(depth, env, f_expr);
                        last_f_expr = Some(f_expr);
                        last_f_val = Some(v);
                        v
                    };
                    if self.vals().is_inert_rigid(f_val) {
                        result = self.neutral_app(f_val, result);
                        continue;
                    }
                    result = self.apply(depth, f_val, result);
                }
                return result;
            }
            let mut buf = [MaybeUninit::uninit(); SPINE];
            let spilled;
            let (head, rev_args) = if let Some(peeled) = self.ctx.peel_apps(e, &mut buf) {
                peeled
            } else {
                spilled = self.ctx.unfold_apps_rev(e);
                (spilled.0, &spilled.1[..])
            };
            let f = self.eval(depth, env, head);
            return self.eval_spine(depth, env, f, rev_args);
        }
        match first {
            Expr::Var { dbj_idx } => self
                .vals()
                .env_lookup(env, dbj_idx)
                .expect("eval: loose bvar"),
            Expr::Sort { level } => {
                let level = match self.vals().env_lsub(env) {
                    Some(ls) => {
                        let ls = self.vals().lsub(ls);
                        self.ctx.subst_level(level, ls.ks, ls.vs)
                    }
                    None => level,
                };
                let level = self.ctx.simplify(level);
                self.mk_sort_hc(level)
            }
            Expr::Const { name, levels } => {
                let levels = match self.vals().env_lsub(env) {
                    Some(ls) => {
                        let ls = self.vals().lsub(ls);
                        self.ctx.subst_levels(levels, ls.ks, ls.vs)
                    }
                    None => levels,
                };
                self.eval_const(name, levels)
            }
            Expr::App { .. } => unreachable!(),
            Expr::Lambda { binder_type, body } => {
                let ce = self.key_env(env, e);
                let loose = self.ctx.loose(body);
                self.mk_lam_hc(binder_type, Closure::mk_eval(ce, body, loose))
            }
            Expr::Pi { binder_type, body } => {
                let dom = self.eval(depth, env, binder_type);
                {
                    let ce = self.key_env(env, e);
                    let loose = self.ctx.loose(body);
                    self.mk_pi_hc(dom, Closure::mk_eval(ce, body, loose))
                }
            }
            Expr::Let { .. } => {
                let mut env = env;
                let mut cursor = e;
                while let Expr::Let { val, body, .. } = self.ctx.ex(cursor) {
                    let vv = self.eval(depth, env, val);
                    env = self.env_extend(env, vv);
                    cursor = body;
                }
                self.eval(depth, env, cursor)
            }
            Expr::Proj {
                ty_name,
                idx,
                structure,
            } => {
                let vs = self.eval(depth, env, structure);
                self.do_proj(depth, ty_name, idx, vs)
            }
            Expr::NatLit { lit } => self.mk_natlit_hc(lit),
            Expr::StringLit { lit } => self.mk_strlit_hc(lit),
        }
    }

    pub(crate) fn placeholder(&mut self) -> V {
        if let Some(v) = self.tc_cache.placeholder {
            return v;
        }
        let v = self.mk_sort_hc(self.ctx.zero());
        self.tc_cache.placeholder = Some(v);
        v
    }

    #[inline(always)]
    fn eval_spine(&mut self, depth: u32, env: E, mut f: V, rev_args: &[ExprId]) -> V {
        if let Value::Rigid {
            head: RigidHead::Recursor(..) | RigidHead::QuotConst(..),
            spine,
        } = self.val(f)
            && self.vals().is_head(spine)
        {
            let mut args = smallvec::SmallVec::<[V; 16]>::with_capacity(rev_args.len());
            for &a in rev_args.iter().rev() {
                args.push(self.eval(depth, env, a));
            }
            if let Some(r) = self.fire_saturated(depth, f, &args) {
                return r;
            }
            return self.apply_many(depth, f, &args);
        }
        let mut i = rev_args.len();
        while i > 0 {
            if let Value::Lam { body: clo, .. } = self.val(f) {
                let mut benv = clo.env;
                let mut body = clo.body;
                loop {
                    i -= 1;
                    let a = self.eval(depth, env, rev_args[i]);
                    benv = self.env_extend(benv, a);
                    match self.ctx.ex(body) {
                        Expr::Lambda { body: inner, .. } if i > 0 => body = inner,
                        _ => break,
                    }
                }
                f = self.eval(depth, benv, body);
            } else {
                i -= 1;
                let a = self.eval(depth, env, rev_args[i]);
                f = self.apply(depth, f, a);
            }
        }
        f
    }

    fn fire_saturated(&mut self, depth: u32, f: V, args: &[V]) -> Option<V> {
        let Value::Rigid { head, spine } = self.val(f) else {
            return None;
        };
        if !self.vals().is_head(spine) {
            return None;
        }
        match head {
            RigidHead::Recursor(name, levels) => {
                let env = self.env;
                let rec = env.get_recursor(name)?;
                let major = *args.get(rec.major_idx())?;
                match self.val(major) {
                    Value::Rigid {
                        head: RigidHead::Ctor(..),
                        ..
                    }
                    | Value::NatLit { .. }
                    | Value::StrLit { .. } => self.fire_recursor(depth, rec, levels, args, major),
                    _ => None,
                }
            }
            RigidHead::QuotConst(name, _) => {
                let cache = self.ctx.export_file.name_cache;
                let major_idx = if Some(name) == cache.quot_lift {
                    5
                } else if Some(name) == cache.quot_ind {
                    4
                } else {
                    return None;
                };
                let major = *args.get(major_idx)?;
                match self.val(major) {
                    Value::Rigid {
                        head: RigidHead::QuotConst(..),
                        ..
                    } => self.fire_quot(depth, name, args, major),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn const_kind(&mut self, name: NameId) -> ConstKind {
        match self.env.get_declar(name) {
            Some(Declar::Definition { .. } | Declar::Theorem { .. }) => ConstKind::Unfoldable,
            Some(Declar::Constructor(_)) => ConstKind::Ctor,
            Some(Declar::Recursor(_)) => ConstKind::Recursor,
            Some(Declar::Quot { .. }) => ConstKind::Quot,
            Some(Declar::Inductive(_)) => ConstKind::Inductive,
            Some(Declar::Axiom { .. } | Declar::Opaque { .. }) | None => ConstKind::Axiom,
        }
    }

    fn declar_val(&mut self, name: NameId) -> Option<(LevelsId, ExprId)> {
        self.env.get_declar_val(name)
    }

    pub(crate) fn eval_const(&mut self, name: NameId, levels: LevelsId) -> V {
        memo!(
            self.tc_cache.const_head_value_cache,
            (name, levels),
            match self.const_kind(name) {
                ConstKind::Unfoldable => self.mk_unfold_head(name, levels),
                ConstKind::Ctor => self.mk_head_hc(RigidHead::Ctor(name, levels)),
                ConstKind::Recursor => self.mk_head_hc(RigidHead::Recursor(name, levels)),
                ConstKind::Quot => self.mk_head_hc(RigidHead::QuotConst(name, levels)),
                ConstKind::Inductive => self.mk_head_hc(RigidHead::Inductive(name, levels)),
                ConstKind::Axiom => self.mk_head_hc(RigidHead::Axiom(name, levels)),
            }
        )
    }

    pub(crate) fn const_result_level(&mut self, name: NameId, levels: LevelsId) -> Option<LevelId> {
        if let Some(cached) = self.tc_cache.const_result_level_cache.get(&(name, levels)) {
            return Some(cached);
        }
        let head_ty = self.const_head_type(name, levels);
        let mut cur = head_ty;
        let mut binder_depth = 0u32;
        loop {
            let cur_f = self.force_all(binder_depth, cur);
            match self.val(cur_f) {
                Value::Pi { domain, body } => {
                    let fresh = self.mk_bvar_hc(binder_depth, domain);
                    cur = self.apply_closure(binder_depth + 1, body, fresh, Some(domain));
                    binder_depth += 1;
                }
                Value::Sort { level } => {
                    let l = self.ctx.simplify(level);
                    self.tc_cache
                        .const_result_level_cache
                        .insert((name, levels), l);
                    return Some(l);
                }
                _ => return None,
            }
        }
    }

    pub(crate) fn const_head_type(&mut self, name: NameId, levels: LevelsId) -> V {
        memo!(self.tc_cache.const_head_type_cache, (name, levels), {
            let Some(d) = self.env.get_declar(name) else {
                reject!("const_head_type: unknown const {}", self.ctx.display(name))
            };
            let info = *d.info();
            ensure!(
                self.ctx.levels(info.uparams).len() == self.ctx.levels(levels).len(),
                "wrong number of universe levels for {}",
                self.ctx.display(name)
            );
            self.eval_inst(info.ty, info.uparams, levels)
        })
    }

    pub(crate) fn lam_domain(&mut self, depth: u32, v: V) -> V {
        match self.val(v) {
            Value::Lam { binder_type, body } => {
                if let Some(d) = self.vals().step(v) {
                    return d;
                }
                let d = self.eval(depth, body.env, binder_type);
                self.vals_mut().set_step(v, d);
                d
            }
            Value::Pi { domain, .. } => domain,
            _ => panic!("lam_domain: not a Lam/Pi"),
        }
    }

    fn neutral_app(&mut self, f: V, a: V) -> V {
        self.tc_cache.vals.app(f, a)
    }

    #[inline(always)]
    pub(crate) fn apply(&mut self, depth: u32, f: V, a: V) -> V {
        match self.vals().find_inert_app(f, a) {
            Some(v) => v,
            None => self.apply_new(depth, f, a),
        }
    }

    #[inline(never)]
    fn apply_new(&mut self, depth: u32, f: V, a: V) -> V {
        match self.val(f) {
            Value::Lam { body: clo, .. } => {
                let clo_env = clo.env;
                let clo_body = clo.body;
                let env = self.env_extend(clo_env, a);
                self.eval(depth, env, clo_body)
            }
            Value::Rigid { head, spine } => {
                let head_copy = head;
                if self.nat_extension
                    && let RigidHead::Ctor(name, _) = head_copy
                    && Some(name) == self.ctx.export_file.name_cache.nat_succ
                {
                    let new_spine = self.spine_snoc_hc(spine, Elim::app(a));
                    return self.try_fire_rigid(depth, head_copy, new_spine);
                }
                self.neutral_app(f, a)
            }
            Value::Unfold { .. } => self.neutral_app(f, a),
            _ => reject!("apply: ill-typed application"),
        }
    }

    pub(crate) fn apply_many(&mut self, depth: u32, f0: V, args: &[V]) -> V {
        let mut f = f0;
        let mut i = 0usize;
        while i < args.len() {
            let Value::Lam { body: clo, .. } = self.val(f) else {
                f = self.apply(depth, f, args[i]);
                i += 1;
                continue;
            };
            let mut env = self.env_extend(clo.env, args[i]);
            let mut body = clo.body;
            i += 1;
            while i < args.len() {
                let Expr::Lambda { body: inner, .. } = self.ctx.ex(body) else {
                    break;
                };
                env = self.env_extend(env, args[i]);
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
        clo: Closure,
        v: V,
        binder_ty: Option<V>,
    ) -> V {
        let env = self.env_extend(clo.env, v);
        match clo.ctx {
            None => self.eval(depth, env, clo.body),
            Some(clo_ctx) => {
                let ty = binder_ty.expect("apply_closure: infer closure without a binder type");
                let ctx = self.ctx_extend(clo_ctx, ty);
                self.infer_value(
                    crate::checker::tc::InferFlag::InferOnly,
                    depth,
                    env,
                    ctx,
                    clo.body,
                )
            }
        }
    }

    fn try_fire_rigid(&mut self, depth: u32, head: RigidHead, spine: S) -> V {
        if self.nat_extension
            && let RigidHead::Ctor(name, _) = head
            && Some(name) == self.ctx.export_file.name_cache.nat_succ
            && let Spine::Snoc { prev, elim, .. } = self.vals().spine(spine)
            && self.vals().is_head(prev)
            && let ElimView::App(arg) = elim.view()
            && let Some(n) = self.value_to_bignum_at(depth, arg, false)
        {
            let succ_lit = n + 1u8;
            if let Some(p) = self.ctx.alloc_bignum(succ_lit) {
                return self.mk_natlit_hc(p);
            }
        }
        spine
    }

    pub(crate) fn value_type(&mut self, depth: u32, v: V) -> V {
        if let Some(t) = self.vals().ty(v) {
            return t;
        }
        let t = self.value_type_uncached(depth, v);
        self.vals_mut().set_ty(v, t);
        t
    }

    fn value_type_uncached(&mut self, depth: u32, v: V) -> V {
        match self.val(v) {
            Value::Sort { level } => {
                let s = self.ctx.succ(level);
                let s = self.ctx.simplify(s);
                self.mk_sort_hc(s)
            }
            Value::NatLit { .. } => {
                let n = self
                    .ctx
                    .export_file
                    .name_cache
                    .nat
                    .expect("value_type: Nat name missing");
                let levels = self.ctx.alloc_levels(&[]);
                self.mk_head_hc(RigidHead::Inductive(n, levels))
            }
            Value::StrLit { .. } => {
                let n = self
                    .ctx
                    .export_file
                    .name_cache
                    .string
                    .expect("value_type: String name missing");
                let levels = self.ctx.alloc_levels(&[]);
                self.mk_head_hc(RigidHead::Inductive(n, levels))
            }
            Value::Rigid { head, spine } => {
                let head_ty = self.rigid_head_type(depth, head);
                let prev = self.mk_head_hc(head);
                self.spine_type_with_value(depth, head_ty, prev, spine)
            }
            Value::Unfold { head, spine, .. } => {
                let head_ty = self.const_head_type(head.name, head.levels);
                let prev = self.mk_unfold_head(head.name, head.levels);
                self.spine_type_with_value(depth, head_ty, prev, spine)
            }
            Value::Pi { .. } | Value::Lam { .. } => panic!("value_type: Pi/Lam not supported"),
        }
    }

    fn rigid_head_type(&mut self, _depth: u32, head: RigidHead) -> V {
        match head {
            RigidHead::BVar(_, ty) => ty,
            RigidHead::Axiom(n, ls)
            | RigidHead::Ctor(n, ls)
            | RigidHead::Recursor(n, ls)
            | RigidHead::QuotConst(n, ls)
            | RigidHead::Inductive(n, ls) => self.const_head_type(n, ls),
        }
    }

    fn spine_type_with_value(&mut self, depth: u32, mut ty: V, prev_head: V, spine: S) -> V {
        let mut prev = prev_head;
        for elim in self.vals().spine_to_vec(spine) {
            match elim.view() {
                ElimView::App(a) => {
                    let ty_f = self.force_all(depth, ty);
                    match self.val(ty_f) {
                        Value::Pi { domain, body } => {
                            ty = self.apply_closure(depth, body, a, Some(domain));
                        }
                        _ => reject!("spine_type_with_value: expected Pi"),
                    }
                    prev = self.apply(depth, prev, a);
                }
                ElimView::Proj { ty_name, idx } => {
                    ty = self
                        .proj_field_type_with(depth, prev, ty, ty_name, idx)
                        .unwrap_or_else(|| reject!("spine_type_with_value: bad proj"));
                    prev = self.do_proj(depth, ty_name, idx, prev);
                }
            }
        }
        ty
    }

    pub(crate) fn whnf_head(&mut self, depth: u32, v: V) -> V {
        if let Some(w) = self.vals().whnf(v) {
            return w;
        }
        let w = self.whnf_head_uncached(depth, v);
        self.vals_mut().set_whnf(v, w);
        w
    }

    fn whnf_head_uncached(&mut self, depth: u32, v: V) -> V {
        if let Some(r) = self.store_lookup(depth, v) {
            return r;
        }
        let mut cur = v;
        let mut steps = 0u32;
        let result = loop {
            match self.val(cur) {
                Value::Unfold { .. } => {
                    let next = self.unfold_value(depth, cur);
                    if next == cur {
                        break cur;
                    }
                    steps += 1;
                    cur = next;
                }
                Value::Rigid {
                    head: RigidHead::Recursor(..) | RigidHead::QuotConst(..),
                    ..
                } => match self.iota_value(depth, cur) {
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

    pub(crate) fn nat_red_defer(&self, name: NameId, args: &[V]) -> bool {
        use crate::term::name::NatRed::{Add, Mul, Pow, Sub};
        let structural_on_second = matches!(
            self.ctx.export_file.nat_red(name),
            Some(Add | Sub | Mul | Pow)
        );
        if !structural_on_second || args.len() != 2 {
            return false;
        }
        if let Value::NatLit { lit } = self.val(args[1]) {
            self.ctx.bignum(lit).bits() > 8
        } else {
            false
        }
    }
}
