use crate::env::Declar;
use crate::expr::Expr;
use crate::tc::{InferFlag, TypeChecker};
use crate::util::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use crate::value::{self, Closure, RigidHead, Value, C, E, V};

use Expr::*;
use InferFlag::*;

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

impl<'x, 't, 'p> TypeChecker<'x, 't, 'p> {
    fn uparam_scope(&self) -> CheckScope<'t> {
        match self.declar_info {
            Some(info) => CheckScope::Under(info.uparams),
            None => CheckScope::NoUparams,
        }
    }

    pub(crate) fn ensure_sort_v(&mut self, depth: u32, v: V<'t>) -> LevelPtr<'t> {
        match self.force_all(depth, v) {
            Value::Sort { level , .. } => *level,
            _ => panic!("expected a sort"),
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
        match self.ctx.read_expr_ref(a) {
            Var { .. } | Sort { .. } | Const { .. } | NatLit { .. } | StringLit { .. } =>
                self.eval(depth, env, a),
            _ => self.mk_thunk_hc(env, a),
        }
    }

    fn lit_inductive_type(&mut self, n: Option<NamePtr<'t>>) -> V<'t> {
        let name = n.expect("infer: literal type name missing");
        let levels = self.ctx.alloc_levels_slice(&[]);
        let empty = self.empty_spine();
        value::mk_rigid_head_with_empty(self.arena, RigidHead::Inductive(name, levels), empty)
    }

    pub(crate) fn infer_value(
        &mut self,
        flag: InferFlag,
        depth: u32,
        env: E<'t>,
        ctx: C<'t>,
        e: ExprPtr<'t>,
    ) -> V<'t> {
        match self.ctx.read_expr(e) {
            Var { dbj_idx, .. } => return ctx.lookup(dbj_idx).expect("loose bvar in infer"),
            Sort { level, .. } => {
                if let (Check, Some(info)) = (flag, self.declar_info) {
                    assert!(
                        self.ctx.all_uparams_defined(level, info.uparams),
                        "universe parameter not declared by the current declaration"
                    );
                }
                let sc = self.ctx.succ(level);
                let sc = self.ctx.simplify(sc);
                return value::mk_sort(self.arena, sc);
            }
            Const { name, levels, .. } => {
                if let (Check, Some(info)) = (flag, self.declar_info) {
                    for l in self.ctx.read_levels(levels).iter().copied() {
                        assert!(self.ctx.all_uparams_defined(l, info.uparams));
                    }
                }
                return self.const_head_type(name, levels);
            }
            NatLit { .. } => {
                assert!(self.ctx.export_file.config.nat_extension);
                return self.lit_inductive_type(self.ctx.export_file.name_cache.nat);
            }
            StringLit { .. } => {
                assert!(self.ctx.export_file.config.string_extension);
                return self.lit_inductive_type(self.ctx.export_file.name_cache.string);
            }
            App { .. } | Lambda { .. } | Pi { .. } | Let { .. } | Proj { .. } => {}
        }

        let key = (self.key_env(env, e) as *const value::Env<'t> as usize, e);
        let scope = self.uparam_scope();
        if let Some(cached) = self.tc_cache.type_cache.get(&key).copied() {
            if flag == InferOnly || cached.checked_under == scope {
                return cached.result;
            }
        }

        let r = match self.ctx.read_expr(e) {
            App { .. } => self.infer_app_v(flag, depth, env, ctx, e),
            Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let dom = self.arg_value(depth, env, binder_type);
                if flag == Check {
                    self.infer_sort_of_v(flag, depth, env, ctx, binder_type);
                    let fresh = self.mk_bvar_hc(depth, dom);
                    let env2 = value::env_extend(self.arena, env, fresh);
                    let ctx2 = value::ctx_extend(self.arena, ctx, dom);
                    self.infer_value(flag, depth + 1, env2, ctx2, body);
                }
                let clo = Closure::mk_infer(self.key_env(env, e), ctx, body);
                value::mk_pi(self.arena, binder_name, binder_style, dom, clo)
            }
            Pi { binder_type, body, .. } => {
                let l1 = self.infer_sort_of_v(flag, depth, env, ctx, binder_type);
                let dom = self.arg_value(depth, env, binder_type);
                let fresh = self.mk_bvar_hc(depth, dom);
                let env2 = value::env_extend(self.arena, env, fresh);
                let ctx2 = value::ctx_extend(self.arena, ctx, dom);
                let l2 = self.infer_sort_of_v(flag, depth + 1, env2, ctx2, body);
                let im = self.ctx.imax(l1, l2);
                let im = self.ctx.simplify(im);
                value::mk_sort(self.arena, im)
            }
            Let { data: &crate::expr::LetData { binder_type, val, body, .. }, .. } => {
                let dom = self.arg_value(depth, env, binder_type);
                if flag == Check {
                    self.infer_sort_of_v(flag, depth, env, ctx, binder_type);
                    let val_ty = self.infer_value(flag, depth, env, ctx, val);
                    assert!(self.conv_types_at(depth, dom, val_ty), "let def_eq failed");
                }
                let slot = self.arg_value(depth, env, val);
                let env2 = value::env_extend(self.arena, env, slot);
                let ctx2 = value::ctx_extend(self.arena, ctx, dom);
                self.infer_value(flag, depth, env2, ctx2, body)
            }
            Proj { ty_name, idx, structure, .. } => self.infer_proj_v(flag, depth, env, ctx, ty_name, idx, structure),
            _ => unreachable!(),
        };

        let checked_under = if flag == Check { scope } else { CheckScope::Unchecked };
        self.tc_cache.type_cache.insert(key, CachedType { result: r, checked_under });
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
        let (fun, mut args) = self.ctx.unfold_apps_stack(self.arena, e);
        let mut fty = self.infer_value(flag, depth, env, ctx, fun);
        while let Some(arg) = args.pop() {
            let fty_f = self.force_all(depth, fty);
            let (domain, body) = match fty_f {
                Value::Pi { domain, body, .. } => (*domain, body),
                _ => panic!("expected a pi type"),
            };
            if flag == Check {
                let arg_ty = self.infer_value(flag, depth, env, ctx, arg);
                assert!(self.conv_types_at(depth, domain, arg_ty), "app arg def_eq failed");
            }
            if body.ctx.is_none() && self.ctx.num_loose_bvars(body.body) == 0 {
                fty = self.eval(depth, body.env, body.body);
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
            Value::Rigid { head: RigidHead::Inductive(n, ls), spine, .. } => (*n, *ls, *spine),
            _ => panic!("projection structure type is not an inductive"),
        };
        assert!(ind_name == ty_name, "projection type name does not match the structure's inductive");
        let params =
            self.spine_apps(depth, spine).expect("projection structure type has a non-applicative spine");
        let (num_params, num_indices, ctor_name) = {
            let ind = self.env.get_inductive(&ind_name).expect("projection structure type is not an inductive");
            assert!(ind.all_ctor_names.len() == 1, "projection of an inductive without exactly one constructor");
            (usize::from(ind.num_params), usize::from(ind.num_indices), ind.all_ctor_names[0])
        };
        assert!(params.len() == num_params + num_indices, "projection structure type is not fully applied");

        let struct_v = self.arg_value(depth, env, structure);
        let mut cur = self.const_head_type(ctor_name, ind_levels);
        for p in params.iter().take(num_params).copied() {
            match self.force_all(depth, cur) {
                Value::Pi { domain, body, .. } => cur = self.apply_closure(depth, body, p, Some(*domain)),
                _ => panic!("ran out of param telescope in projection"),
            }
        }
        for i in 0..idx {
            match self.force_all(depth, cur) {
                Value::Pi { domain, body, .. } => {
                    if self.ctx.has_loose_bvar(body.body, 0)
                        && struct_ty_is_prop
                        && !self.is_prop_type(depth, domain)
                    {
                        panic!("projection of a non-proof field from a Prop structure")
                    }
                    let prior = self.do_proj(depth, ind_name, i, struct_v);
                    cur = self.apply_closure(depth, body, prior, Some(*domain));
                }
                _ => panic!("ran out of constructor telescope in projection"),
            }
        }
        match self.force_all(depth, cur) {
            Value::Pi { domain, .. } => {
                if struct_ty_is_prop && !self.is_prop_type(depth, domain) {
                    panic!("projection of a non-proof field from a Prop structure")
                }
                *domain
            }
            _ => panic!("ran out of constructor telescope getting projection field"),
        }
    }

    pub(crate) fn check_declar_info_v(&mut self, d: &Declar<'t>) {
        let info = d.info();
        assert!(self.ctx.no_dupes_all_params(info.uparams), "duplicate universe parameters in declaration");
        let empty_env = self.empty_env();
        let empty_ctx = self.empty_ctx();
        let ty_ty = self.infer_value(Check, 0, empty_env, empty_ctx, info.ty);
        let sort = self.ensure_sort_v(0, ty_ty);
        if let Declar::Theorem { .. } = d {
            assert!(self.ctx.is_zero(sort), "theorem type must be Prop (sort 0)");
        }
    }

    pub(crate) fn check_def_like_v(&mut self, d: &Declar<'t>, val: ExprPtr<'t>) {
        self.check_declar_info_v(d);
        let empty_env = self.empty_env();
        let empty_ctx = self.empty_ctx();
        let val_ty = self.infer_value(Check, 0, empty_env, empty_ctx, val);
        let declared = self.eval(0, empty_env, d.info().ty);
        assert!(self.def_eq_at(0, val_ty, declared), "def_eq failed");
    }
}
