// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::env::Declar;
use crate::checker::tc::{InferFlag, TypeChecker};
use crate::checker::value::{self, C, Closure, E, RigidHead, V, Value};
use crate::outcome::{ensure, reject};
use crate::term::expr::Expr;
use crate::term::ptr::{ExprPtr, Id, LevelPtr, LevelsPtr, NamePtr};

use Expr::{App, Const, Lambda, Let, NatLit, Pi, Proj, Sort, StringLit, Var};
use InferFlag::{Check, InferOnly};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CheckScope<'a> {
    Unchecked,
    NoUparams,
    Under(LevelsPtr<'a>),
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct CachedType<'a> {
    pub(crate) result: V<'a>,
    pub(crate) checked_under: CheckScope<'a>,
}

fn atomic_type(v: V<'_>) -> bool {
    match v {
        Value::Sort { .. } | Value::NatLit { .. } | Value::StrLit { .. } => true,
        Value::Rigid { spine, .. } => spine.is_empty(),
        _ => false,
    }
}

fn has_deep_bvar_prefix(mut env: E<'_>) -> bool {
    for _ in 0..64 {
        match env {
            value::Env::Cons {
                v:
                    Value::Rigid {
                        head: RigidHead::BVar(..),
                        ..
                    },
                parent,
                ..
            } => env = parent,
            _ => return false,
        }
    }
    true
}

impl<'t> TypeChecker<'_, 't, '_> {
    fn uparam_scope(&self) -> CheckScope<'t> {
        match self.declar_info {
            Some(info) => CheckScope::Under(info.uparams),
            None => CheckScope::NoUparams,
        }
    }

    pub(crate) fn ensure_sort_v(&mut self, depth: u32, v: V<'t>) -> LevelPtr<'t> {
        match self.force_all(depth, v) {
            Value::Sort { level, .. } => *level,
            _ => reject!("expected a sort"),
        }
    }

    pub(crate) fn infer_sort_of_v(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E<'t>,
        ctx: C<'t>,
        e: ExprPtr<'t>,
    ) -> LevelPtr<'t> {
        let t = self.infer_value(flag, depth, env, ctx, e);
        self.ensure_sort_v(depth, t)
    }

    pub(crate) fn arg_value(&mut self, depth: u32, env: E<'t>, a: ExprPtr<'t>) -> V<'t> {
        self.eval(depth, env, a)
    }

    fn lit_inductive_type(&mut self, n: Option<NamePtr<'t>>) -> V<'t> {
        let name = n.expect("infer: literal type name missing");
        let levels = self.ctx.alloc_levels_slice(&[]);
        self.mk_head_hc(RigidHead::Inductive(name, levels))
    }

    #[inline(always)]
    pub(crate) fn infer_value(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E<'t>,
        ctx: C<'t>,
        e: ExprPtr<'t>,
    ) -> V<'t> {
        if let &Var { dbj_idx, .. } = e.as_ref() {
            return ctx.lookup(dbj_idx).expect("loose bvar in infer");
        }
        self.infer_nonvar(flag, depth, env, ctx, e)
    }

    #[inline(never)]
    fn infer_nonvar(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E<'t>,
        ctx: C<'t>,
        e: ExprPtr<'t>,
    ) -> V<'t> {
        match *e {
            Var { dbj_idx, .. } => return ctx.lookup(dbj_idx).expect("loose bvar in infer"),
            Sort { level, .. } => {
                if let (Check, Some(info)) = (flag, self.declar_info)
                    && !self.ctx.leaf_checked(e)
                {
                    ensure!(
                        level.all_uparams_defined(info.uparams),
                        "universe parameter not declared by the current declaration"
                    );
                    self.ctx.mark_leaf_checked(e);
                }
                let sc = self.ctx.succ(level);
                let sc = self.ctx.simplify(sc);
                return self.mk_sort_hc(sc);
            }
            Const { name, levels, .. } => {
                if let (Check, Some(info)) = (flag, self.declar_info)
                    && !self.ctx.leaf_checked(e)
                {
                    for l in levels.as_ref().iter().copied() {
                        ensure!(l.all_uparams_defined(info.uparams));
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

        let key = (Id::of(self.key_env(env, e)), e);
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
                    && e.num_loose_bvars() == 0
                    && !e.is_local() =>
            {
                Some(info.uparams)
            }
            _ => None,
        };
        let known = reusable.is_some_and(|u| self.ctx.checked_closed.contains(&(e, u)));
        let requested = flag;
        let flag = if known { InferOnly } else { flag };

        let r = match *e {
            App { .. } => self.infer_app_v(flag, depth, env, ctx, e),
            Lambda {
                binder_type, body, ..
            } => {
                let dom = self.arg_value(depth, env, binder_type);
                let mut body_ty = None;
                if flag == Check {
                    self.infer_sort_of_v(flag, depth, env, ctx, binder_type);
                    let fresh = self.mk_bvar_hc(depth, dom);
                    let env2 = self.env_extend(env, fresh);
                    let ctx2 = value::ctx_extend(self.arena, ctx, dom);
                    body_ty = Some(self.infer_value(flag, depth + 1, env2, ctx2, body));
                }
                let clo = match body_ty.filter(|bt| {
                    atomic_type(bt)
                        && bt.is_closed()
                        && std::ptr::eq(*bt, dom)
                        && binder_type.num_loose_bvars() == 0
                        && has_deep_bvar_prefix(env)
                }) {
                    Some(_) => Closure::mk_eval(self.empty_env(), binder_type),
                    None => Closure::mk_infer(self.key_env(env, e), ctx, body),
                };
                self.mk_pi_hc(dom, clo)
            }
            Pi {
                binder_type, body, ..
            } => {
                let l1 = self.infer_sort_of_v(flag, depth, env, ctx, binder_type);
                let dom = self.arg_value(depth, env, binder_type);
                let fresh = self.mk_bvar_hc(depth, dom);
                let env2 = self.env_extend(env, fresh);
                let ctx2 = value::ctx_extend(self.arena, ctx, dom);
                let l2 = self.infer_sort_of_v(flag, depth + 1, env2, ctx2, body);
                let im = self.ctx.imax(l1, l2);
                let im = self.ctx.simplify(im);
                self.mk_sort_hc(im)
            }
            Let {
                data:
                    &crate::term::expr::LetData {
                        binder_type,
                        val,
                        body,
                        ..
                    },
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
                let ctx2 = value::ctx_extend(self.arena, ctx, dom);
                self.infer_value(flag, depth, env2, ctx2, body)
            }
            Proj {
                ty_name,
                idx,
                structure,
                ..
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
        env: E<'t>,
        ctx: C<'t>,
        e: ExprPtr<'t>,
    ) -> V<'t> {
        const SPINE: usize = 16;
        let mut buf = [std::mem::MaybeUninit::<ExprPtr<'t>>::uninit(); SPINE];
        let mut n = 0;
        let mut head = e;
        while let &App { fun, arg, .. } = head.as_ref() {
            if n == SPINE {
                return self.infer_long_app_v(flag, depth, env, ctx, e);
            }
            buf[n].write(arg);
            n += 1;
            head = fun;
        }
        let rev_args = unsafe { std::slice::from_raw_parts(buf.as_ptr().cast::<ExprPtr<'t>>(), n) };
        let mut fty = self.infer_value(flag, depth, env, ctx, head);
        let mut telescope: Option<(E<'t>, ExprPtr<'t>)> = None;
        for &arg in rev_args.iter().rev() {
            if let Some((tenv, t)) = telescope
                && let &Pi {
                    binder_type, body, ..
                } = t.as_ref()
            {
                if flag == Check {
                    let arg_ty = self.infer_value(flag, depth, env, ctx, arg);
                    let domain = self.eval_arg(depth, tenv, binder_type);
                    ensure!(
                        self.conv_types_at(depth, domain, arg_ty),
                        "app arg def_eq failed"
                    );
                }
                let av = if crate::term::expr::ignores_binder(body) {
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
            let (domain, body) = match fty_f {
                Value::Pi { domain, body, .. } => (*domain, body),
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
                if crate::term::expr::ignores_binder(body.body) {
                    fty = self.apply_closure(depth, body, domain, Some(domain));
                } else {
                    let av = self.eval_arg(depth, env, arg);
                    fty = self.apply_closure(depth, body, av, Some(domain));
                }
            } else if body.body.num_loose_bvars() == 0 {
                telescope = Some((body.env, body.body));
            } else {
                let av = if crate::term::expr::ignores_binder(body.body) {
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

    #[inline(never)]
    fn infer_long_app_v(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E<'t>,
        ctx: C<'t>,
        e: ExprPtr<'t>,
    ) -> V<'t> {
        let (fun, mut args) = e.unfold_apps_stack(self.arena);
        let mut fty = self.infer_value(flag, depth, env, ctx, fun);
        while let Some(arg) = args.pop() {
            let fty_f = self.force_all(depth, fty);
            let (domain, body) = match fty_f {
                Value::Pi { domain, body, .. } => (*domain, body),
                _ => reject!("expected a pi type"),
            };
            if flag == Check {
                let arg_ty = self.infer_value(flag, depth, env, ctx, arg);
                ensure!(
                    self.conv_types_at(depth, domain, arg_ty),
                    "app arg def_eq failed"
                );
            }
            if body.ctx.is_none() && body.body.num_loose_bvars() == 0 {
                fty = self.eval(depth, body.env, body.body);
            } else if crate::term::expr::ignores_binder(body.body) {
                fty = self.apply_closure(depth, body, domain, Some(domain));
            } else {
                let av = self.arg_value(depth, env, arg);
                fty = self.apply_closure(depth, body, av, Some(domain));
            }
        }
        fty
    }

    fn infer_proj_v(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E<'t>,
        ctx: C<'t>,
        ty_name: NamePtr<'t>,
        idx: u16,
        structure: ExprPtr<'t>,
    ) -> V<'t> {
        let struct_ty = self.infer_value(flag, depth, env, ctx, structure);
        let struct_ty_f = self.force_all(depth, struct_ty);
        let struct_ty_is_prop = self.is_prop_type(depth, struct_ty_f);
        let (ind_name, ind_levels, spine) = match struct_ty_f {
            Value::Rigid {
                head: RigidHead::Inductive(n, ls),
                spine,
                ..
            } => (*n, *ls, *spine),
            _ => reject!("projection structure type is not an inductive"),
        };
        ensure!(
            ind_name == ty_name,
            "projection type name does not match the structure's inductive"
        );
        let params = spine
            .apps()
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
            match self.force_all(depth, cur) {
                Value::Pi { domain, body, .. } => {
                    cur = self.apply_closure(depth, body, p, Some(*domain));
                }
                _ => reject!("ran out of param telescope in projection"),
            }
        }
        for i in 0..idx {
            match self.force_all(depth, cur) {
                Value::Pi { domain, body, .. } => {
                    if body.body.has_loose_bvar(0)
                        && struct_ty_is_prop
                        && !self.is_prop_type(depth, domain)
                    {
                        reject!("projection of a non-proof field from a Prop structure")
                    }
                    let prior = self.do_proj(depth, ind_name, i, struct_v);
                    cur = self.apply_closure(depth, body, prior, Some(*domain));
                }
                _ => reject!("ran out of constructor telescope in projection"),
            }
        }
        match self.force_all(depth, cur) {
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

    pub(crate) fn check_declar_info_v(&mut self, d: &Declar<'t>) {
        let info = d.info();
        ensure!(
            info.uparams.no_dupes_all_params(),
            "duplicate universe parameters in declaration"
        );
        let empty_env = self.empty_env();
        let empty_ctx = self.empty_ctx();
        let ty_ty = self.infer_value(Check, 0, empty_env, empty_ctx, info.ty);
        let sort = self.ensure_sort_v(0, ty_ty);
        if let Declar::Theorem { .. } = d {
            ensure!(sort.is_always_zero(), "theorem type must be Prop (sort 0)");
        }
    }

    pub(crate) fn check_def_like_v(&mut self, d: &Declar<'t>, val: ExprPtr<'t>) {
        self.check_declar_info_v(d);
        let empty_env = self.empty_env();
        let empty_ctx = self.empty_ctx();
        let val_ty = self.infer_value(Check, 0, empty_env, empty_ctx, val);
        let declared = self.eval(0, empty_env, d.info().ty);
        ensure!(self.def_eq_at(0, val_ty, declared), "def_eq failed");
    }
}
