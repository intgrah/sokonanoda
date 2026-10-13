// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::env::Declar;
use crate::checker::tc::{InferFlag, TypeChecker};
use crate::checker::value::{
    C, Closure, DUMMY, E, EMPTY_CTX, EMPTY_ENV, RigidHead, V, Vals, Value,
};
use crate::outcome::{ensure, reject};
use crate::term::expr::{Expr, ExprNode, SPINE};
use crate::term::id::{ExprId, LevelId, LevelsId, NameId};
use std::mem::MaybeUninit;

use Expr::{App, Const, Lambda, Let, NatLit, Pi, Proj, Sort, StringLit, Var};
use InferFlag::{Check, InferOnly};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CheckScope {
    Unchecked,
    NoUparams,
    Under(LevelsId),
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct CachedType {
    pub(crate) result: V,
    pub(crate) checked_under: CheckScope,
}

fn atomic_type(vals: &Vals, v: V) -> bool {
    match vals.val(v) {
        Value::Sort { .. } | Value::NatLit { .. } | Value::StrLit { .. } => true,
        Value::Rigid { spine, .. } => vals.is_head(spine),
        _ => false,
    }
}

fn has_deep_bvar_prefix(vals: &Vals, mut env: E) -> bool {
    for _ in 0..64 {
        match vals.env_cons(env) {
            Some((v, parent))
                if v != DUMMY
                    && matches!(
                        vals.val(v),
                        Value::Rigid {
                            head: RigidHead::BVar(..),
                            ..
                        }
                    ) =>
            {
                env = parent;
            }
            _ => return false,
        }
    }
    true
}

impl<'t> TypeChecker<'_, 't> {
    fn uparam_scope(&self) -> CheckScope {
        match self.declar_info {
            Some(info) => CheckScope::Under(info.uparams),
            None => CheckScope::NoUparams,
        }
    }

    pub(crate) fn ensure_sort_v(&mut self, depth: u32, v: V) -> LevelId {
        match self.force_all_val(depth, v) {
            Value::Sort { level, .. } => level,
            _ => reject!("expected a sort"),
        }
    }

    pub(crate) fn infer_sort_of_v(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E,
        ctx: C,
        e: ExprId,
    ) -> LevelId {
        let t = self.infer_value(flag, depth, env, ctx, e);
        self.ensure_sort_v(depth, t)
    }

    pub(crate) fn arg_value(&mut self, depth: u32, env: E, a: ExprId) -> V {
        self.eval(depth, env, a)
    }

    fn lit_inductive_type(&mut self, n: Option<NameId>) -> V {
        let name = n.expect("infer: literal type name missing");
        let levels = self.ctx.alloc_levels(&[]);
        self.mk_head_hc(RigidHead::Inductive(name, levels))
    }

    #[inline(always)]
    pub(crate) fn infer_value(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E,
        ctx: C,
        e: ExprId,
    ) -> V {
        let node = *self.ctx.node(e);
        if let Var { dbj_idx } = node.expr {
            return self.vals().ctx_lookup(ctx, dbj_idx).expect("loose bvar in infer");
        }
        self.infer_nonvar(flag, depth, env, ctx, e, node)
    }

    #[inline(never)]
    fn infer_nonvar(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E,
        ctx: C,
        e: ExprId,
        node: ExprNode,
    ) -> V {
        match node.expr {
            Var { dbj_idx } => return self.vals().ctx_lookup(ctx, dbj_idx).expect("loose bvar in infer"),
            Sort { level } => {
                if let (Check, Some(info)) = (flag, self.declar_info)
                    && !self.ctx.leaf_checked(e)
                {
                    ensure!(
                        self.ctx.all_uparams_defined(level, info.uparams),
                        "universe parameter not declared by the current declaration"
                    );
                    self.ctx.mark_leaf_checked(e);
                }
                let sc = self.ctx.succ(level);
                let sc = self.ctx.simplify(sc);
                return self.mk_sort_hc(sc);
            }
            Const { name, levels } => {
                if let (Check, Some(info)) = (flag, self.declar_info)
                    && !self.ctx.leaf_checked(e)
                {
                    for &l in self.ctx.levels(levels) {
                        ensure!(self.ctx.all_uparams_defined(l, info.uparams));
                    }
                    self.ctx.mark_leaf_checked(e);
                }
                return self.const_head_type(name, levels);
            }
            NatLit { .. } => {
                assert!(self.nat_extension);
                return self.lit_inductive_type(self.ctx.export_file.name_cache.nat);
            }
            StringLit { .. } => {
                assert!(self.ctx.export_file.config.string_extension);
                return self.lit_inductive_type(self.ctx.export_file.name_cache.string);
            }
            App { .. } | Lambda { .. } | Pi { .. } | Let { .. } | Proj { .. } => {}
        }

        let key = (self.prune_env(env, node.mask), e);
        let scope = self.uparam_scope();
        if let Some(cached) = self.tc_cache.type_cache.get(&key)
            && (flag == InferOnly || cached.checked_under == scope)
        {
            return cached.result;
        }

        let reusable = match self.declar_info {
            Some(info)
                if flag == Check
                    && self.ordered_declaration
                    && node.loose == 0
                    && !e.is_local() =>
            {
                Some(info.uparams)
            }
            _ => None,
        };
        let known = reusable.is_some_and(|u| self.ctx.checked_closed.contains(&(e, u)));
        let requested = flag;
        let flag = if known { InferOnly } else { flag };

        let r = match node.expr {
            App { .. } => self.infer_app_v(flag, depth, env, ctx, e),
            Lambda { binder_type, body } => {
                let dom = self.arg_value(depth, env, binder_type);
                let mut body_ty = None;
                if flag == Check {
                    self.infer_sort_of_v(flag, depth, env, ctx, binder_type);
                    let fresh = self.mk_bvar_hc(depth, dom);
                    let env2 = self.env_extend(env, fresh);
                    let ctx2 = self.ctx_extend(ctx, dom);
                    body_ty = Some(self.infer_value(flag, depth + 1, env2, ctx2, body));
                }
                let binder_loose = self.ctx.loose(binder_type);
                let reuse = body_ty.is_some_and(|bt| {
                    atomic_type(self.vals(), bt)
                        && self.vals_mut().is_closed(bt)
                        && bt == dom
                        && binder_loose == 0
                        && has_deep_bvar_prefix(self.vals(), env)
                });
                let clo = match reuse.then_some(()) {
                    Some(_) => Closure::mk_eval(EMPTY_ENV, binder_type, binder_loose),
                    None => {
                        let body_loose = self.ctx.loose(body);
                        Closure::mk_infer(self.key_env(env, e), ctx, body, body_loose)
                    }
                };
                self.mk_pi_hc(dom, clo)
            }
            Pi { binder_type, body } => {
                let l1 = self.infer_sort_of_v(flag, depth, env, ctx, binder_type);
                let dom = self.arg_value(depth, env, binder_type);
                let fresh = self.mk_bvar_hc(depth, dom);
                let env2 = self.env_extend(env, fresh);
                let ctx2 = self.ctx_extend(ctx, dom);
                let l2 = self.infer_sort_of_v(flag, depth + 1, env2, ctx2, body);
                let im = self.ctx.imax(l1, l2);
                let im = self.ctx.simplify(im);
                self.mk_sort_hc(im)
            }
            Let {
                binder_type,
                val,
                body,
                ..
            } => {
                let dom = self.arg_value(depth, env, binder_type);
                if flag == Check {
                    self.infer_sort_of_v(flag, depth, env, ctx, binder_type);
                    let val_ty = self.infer_value(flag, depth, env, ctx, val);
                    ensure!(self.conv_types_at(depth, dom, val_ty), "let def_eq failed");
                }
                let slot = self.arg_value(depth, env, val);
                let env2 = self.env_extend(env, slot);
                let ctx2 = self.ctx_extend(ctx, dom);
                self.infer_value(flag, depth, env2, ctx2, body)
            }
            Proj {
                ty_name,
                idx,
                structure,
            } => self.infer_proj_v(flag, depth, env, ctx, ty_name, idx, structure),
            _ => unreachable!(),
        };

        if let (Some(u), false) = (reusable, known) {
            self.ctx.checked_closed.insert((e, u));
        }
        let checked_under = if requested == Check {
            scope
        } else {
            CheckScope::Unchecked
        };
        self.tc_cache.type_cache.insert(
            key,
            CachedType {
                result: r,
                checked_under,
            },
        );
        r
    }

    fn infer_app_v(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E,
        ctx: C,
        e: ExprId,
    ) -> V {
        let mut buf = [MaybeUninit::uninit(); SPINE];
        let spilled;
        let (head, rev_args) = if let Some(peeled) = self.ctx.peel_apps(e, &mut buf) {
            peeled
        } else {
            spilled = self.ctx.unfold_apps_rev(e);
            (spilled.0, &spilled.1[..])
        };
        let mut fty = self.infer_value(flag, depth, env, ctx, head);
        let mut telescope: Option<(E, ExprId)> = None;
        for &arg in rev_args.iter().rev() {
            if let Some((tenv, t)) = telescope
                && let Pi { binder_type, body } = self.ctx.ex(t)
            {
                if flag == Check {
                    let arg_ty = self.infer_value(flag, depth, env, ctx, arg);
                    let domain = self.eval_arg(depth, tenv, binder_type);
                    ensure!(
                        self.conv_types_at(depth, domain, arg_ty),
                        "app arg def_eq failed"
                    );
                }
                let av = if self.ctx.ignores_binder(body) {
                    self.placeholder()
                } else {
                    self.eval_arg(depth, env, arg)
                };
                telescope = Some((self.env_extend(tenv, av), body));
                continue;
            }
            if let Some((tenv, t)) = telescope.take() {
                fty = self.eval(depth, tenv, t);
            }
            let fty_f = self.force_all(depth, fty);
            let (domain, body) = match self.val(fty_f) {
                Value::Pi { domain, body, .. } => (domain, body),
                _ => reject!("expected a pi type"),
            };
            if flag == Check {
                let arg_ty = self.infer_value(flag, depth, env, ctx, arg);
                ensure!(
                    self.conv_types_at(depth, domain, arg_ty),
                    "app arg def_eq failed"
                );
            }
            if body.ctx.is_some() {
                if self.ctx.ignores_binder(body.body) {
                    fty = self.apply_closure(depth, body, domain, Some(domain));
                } else {
                    let av = self.eval_arg(depth, env, arg);
                    fty = self.apply_closure(depth, body, av, Some(domain));
                }
            } else if body.loose == 0 {
                telescope = Some((body.env, body.body));
            } else {
                let av = if self.ctx.ignores_binder(body.body) {
                    self.placeholder()
                } else {
                    self.eval_arg(depth, env, arg)
                };
                telescope = Some((self.env_extend(body.env, av), body.body));
            }
        }
        if let Some((tenv, t)) = telescope {
            fty = self.eval(depth, tenv, t);
        }
        fty
    }

    fn infer_proj_v(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E,
        ctx: C,
        ty_name: NameId,
        idx: u16,
        structure: ExprId,
    ) -> V {
        let struct_ty = self.infer_value(flag, depth, env, ctx, structure);
        let struct_ty_f = self.force_all(depth, struct_ty);
        let struct_ty_is_prop = self.is_prop_type(depth, struct_ty_f);
        let (ind_name, ind_levels, spine) = match self.val(struct_ty_f) {
            Value::Rigid {
                head: RigidHead::Inductive(n, ls),
                spine,
                ..
            } => (n, ls, spine),
            _ => reject!("projection structure type is not an inductive"),
        };
        ensure!(
            ind_name == ty_name,
            "projection type name does not match the structure's inductive"
        );
        let params = self
            .vals()
            .spine_apps(spine)
            .expect("projection structure type has a non-applicative spine");
        let (num_params, num_indices, ctor_name) = {
            let ind = self
                .env
                .get_inductive(ind_name)
                .expect("projection structure type is not an inductive");
            ensure!(
                ind.all_ctor_names.len() == 1,
                "projection of an inductive without exactly one constructor"
            );
            (
                usize::from(ind.num_params),
                usize::from(ind.num_indices),
                ind.all_ctor_names[0],
            )
        };
        ensure!(
            params.len() == num_params + num_indices,
            "projection structure type is not fully applied"
        );

        let struct_v = self.arg_value(depth, env, structure);
        let mut cur = self.const_head_type(ctor_name, ind_levels);
        for p in params.iter().take(num_params).copied() {
            match self.force_all_val(depth, cur) {
                Value::Pi { domain, body, .. } => {
                    cur = self.apply_closure(depth, body, p, Some(domain));
                }
                _ => reject!("ran out of param telescope in projection"),
            }
        }
        for i in 0..idx {
            match self.force_all_val(depth, cur) {
                Value::Pi { domain, body, .. } => {
                    if self.ctx.has_loose_bvar(body.body, 0)
                        && struct_ty_is_prop
                        && !self.is_prop_type(depth, domain)
                    {
                        reject!("projection of a non-proof field from a Prop structure")
                    }
                    let prior = self.do_proj(depth, ind_name, i, struct_v);
                    cur = self.apply_closure(depth, body, prior, Some(domain));
                }
                _ => reject!("ran out of constructor telescope in projection"),
            }
        }
        match self.force_all_val(depth, cur) {
            Value::Pi { domain, .. } => {
                ensure!(
                    !struct_ty_is_prop || self.is_prop_type(depth, domain),
                    "projection of a non-proof field from a Prop structure"
                );
                domain
            }
            _ => reject!("ran out of constructor telescope getting projection field"),
        }
    }

    pub(crate) fn check_declar_info_v(&mut self, d: &Declar) {
        let info = d.info();
        ensure!(
            self.ctx.no_dupes_all_params(info.uparams),
            "duplicate universe parameters in declaration"
        );
        let empty_env = EMPTY_ENV;
        let empty_ctx = EMPTY_CTX;
        let ty_ty = self.infer_value(Check, 0, empty_env, empty_ctx, info.ty);
        let sort = self.ensure_sort_v(0, ty_ty);
        if let Declar::Theorem { .. } = d {
            ensure!(
                self.ctx.is_always_zero(sort),
                "theorem type must be Prop (sort 0)"
            );
        }
    }

    pub(crate) fn check_def_like_v(&mut self, d: &Declar, val: ExprId) {
        self.check_declar_info_v(d);
        let empty_env = EMPTY_ENV;
        let empty_ctx = EMPTY_CTX;
        let val_ty = self.infer_value(Check, 0, empty_env, empty_ctx, val);
        let declared = self.eval(0, empty_env, d.info().ty);
        ensure!(self.def_eq_at(0, val_ty, declared), "def_eq failed");
    }
}
