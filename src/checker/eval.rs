use crate::checker::env::Declar;
use crate::checker::tc::TypeChecker;
use crate::checker::value::{self, Closure, Elim, ElimView, RigidHead, Spine, Value, E, S, V};
use crate::term::expr::Expr;
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use std::cell::OnceCell;
use std::collections::hash_map::Entry;

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
            Expr::App { .. }
                | Expr::Proj { .. }
                | Expr::Let { .. }
                | Expr::Pi { .. }
                | Expr::Lambda { .. }
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
            if let &Expr::App {
                fun: f2, arg: a2, ..
            } = self.ctx.read_expr_ref(arg)
            {
                let first_fun = fun;
                let mut all_same = fun == f2;
                let mut count = 2u32;
                let mut cur = a2;
                let leaf_expr;
                loop {
                    match self.ctx.read_expr_ref(cur) {
                        &Expr::App {
                            fun: fn3, arg: an3, ..
                        } => {
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
                    if let Value::Rigid { head, .. } = f_val {
                        let is_nat_succ = nat_ext
                            && matches!(*head, RigidHead::Ctor(name, _) if Some(name) == self.ctx.export_file.name_cache.nat_succ);
                        if !is_nat_succ {
                            for _ in 0..count {
                                result = self.neutral_app(f_val, result);
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
                while let &Expr::App {
                    fun: fn3, arg: an3, ..
                } = self.ctx.read_expr_ref(cur2)
                {
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
                    if let Value::Rigid { head, .. } = f_val {
                        let is_nat_succ = nat_ext
                            && matches!(*head, RigidHead::Ctor(name, _) if Some(name) == self.ctx.export_file.name_cache.nat_succ);
                        if !is_nat_succ {
                            result = self.neutral_app(f_val, result);
                            continue;
                        }
                    }
                    result = self.apply(depth, f_val, result);
                }
                return result;
            }
            let mut arg_exprs = smallvec::SmallVec::<[ExprPtr<'t>; 16]>::new();
            arg_exprs.push(arg);
            let mut head = fun;
            while let &Expr::App { fun, arg, .. } = self.ctx.read_expr_ref(head) {
                arg_exprs.push(arg);
                head = fun;
            }
            let f = self.eval(depth, env, head);
            let mut args = smallvec::SmallVec::<[V<'t>; 16]>::with_capacity(arg_exprs.len());
            for &a in arg_exprs.iter().rev() {
                args.push(self.eval(depth, env, a));
            }
            if let Some(r) = self.fire_saturated(depth, f, &args) {
                return r;
            }
            return self.apply_many(depth, f, &args);
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
            Expr::Lambda {
                binder_type, body, ..
            } => {
                let ce = self.key_env(env, e);
                value::mk_lam(self.arena, binder_type, Closure::mk_eval(ce, body))
            }
            Expr::Pi {
                binder_type, body, ..
            } => {
                let dom = self.eval(depth, env, binder_type);
                {
                    let ce = self.key_env(env, e);
                    value::mk_pi(self.arena, dom, Closure::mk_eval(ce, body))
                }
            }
            Expr::Let { .. } => {
                let mut env = env;
                let mut cursor = e;
                while let Expr::Let {
                    data: &crate::term::expr::LetData { val, body, .. },
                    ..
                } = self.ctx.read_expr(cursor)
                {
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
                ..
            } => {
                let vs = self.eval(depth, env, structure);
                self.do_proj(depth, ty_name, idx, vs)
            }
            Expr::NatLit { ptr, .. } => value::mk_natlit(self.arena, ptr),
            Expr::StringLit { ptr, .. } => value::mk_strlit(self.arena, ptr),
        }
    }

    fn fire_saturated(&mut self, depth: u32, f: V<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        let Value::Rigid {
            head,
            spine: Spine::Empty,
            ..
        } = f
        else {
            return None;
        };
        match *head {
            RigidHead::Recursor(name, levels) => {
                let env = self.env;
                let rec = env.get_recursor(&name)?;
                let major = self.force_thunk(depth, *args.get(rec.major_idx())?);
                match major {
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
                let major = self.force_thunk(depth, *args.get(major_idx)?);
                match major {
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
            ConstKind::Ctor => {
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Ctor(name, levels), empty)
            }
            ConstKind::Recursor => value::mk_rigid_head_with_empty(
                self.arena,
                RigidHead::Recursor(name, levels),
                empty,
            ),
            ConstKind::Quot => value::mk_rigid_head_with_empty(
                self.arena,
                RigidHead::QuotConst(name, levels),
                empty,
            ),
            ConstKind::Inductive => value::mk_rigid_head_with_empty(
                self.arena,
                RigidHead::Inductive(name, levels),
                empty,
            ),
            ConstKind::Axiom => {
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Axiom(name, levels), empty)
            }
        };
        v.mark_canonical();
        self.tc_cache
            .const_head_value_cache
            .insert((name, levels), v);
        v
    }

    pub(crate) fn const_result_level(
        &mut self,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<LevelPtr<'t>> {
        if let Some(cached) = self
            .tc_cache
            .const_result_level_cache
            .get(&(name, levels))
            .copied()
        {
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
                Value::Sort { level, .. } => {
                    let l = self.ctx.simplify(*level);
                    self.tc_cache
                        .const_result_level_cache
                        .insert((name, levels), l);
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
        self.tc_cache
            .const_head_type_cache
            .insert((name, levels), v);
        v
    }

    #[inline]
    pub(crate) fn force_thunk(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        if let Value::Thunk {
            env, expr, forced, ..
        } = v
        {
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
            Value::Lam {
                binder_type, body, ..
            } => {
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

    fn neutral_app(&mut self, f: V<'t>, a: V<'t>) -> V<'t> {
        let f = self.canonicalize_for_spine(f);
        let a = self.canonicalize_for_spine(a);
        let key = (
            f as *const Value<'t> as usize,
            a as *const Value<'t> as usize,
        );
        match self.tc_cache.app_hc.entry(key) {
            Entry::Occupied(o) => o.get(),
            Entry::Vacant(slot) => {
                let (v, spine) = match f {
                    Value::Rigid { head, spine, .. } => {
                        let spine = value::spine_snoc(self.arena, spine, Elim::app(a));
                        (value::mk_rigid(self.arena, *head, spine), spine)
                    }
                    Value::Unfold {
                        head,
                        spine,
                        head_value,
                        ..
                    } => {
                        let spine = value::spine_snoc(self.arena, spine, Elim::app(a));
                        (
                            value::mk_unfold(self.arena, head.name, head.levels, spine, head_value),
                            spine,
                        )
                    }
                    _ => unreachable!(),
                };
                // Both inputs have passed canonicalization. Literal values do
                // not have a canonical flag, but are interned by content there.
                spine.mark_canonical();
                v.mark_canonical();
                slot.insert(v)
            }
        }
    }

    #[inline]
    pub(crate) fn apply(&mut self, depth: u32, f: V<'t>, a: V<'t>) -> V<'t> {
        match f {
            Value::Lam { body: clo, .. } => {
                let clo_env = clo.env;
                let clo_body = clo.body;
                let env = self.env_extend(clo_env, a);
                self.eval(depth, env, clo_body)
            }
            Value::Rigid { head, spine, .. } => {
                let head_copy = *head;
                if self.nat_extension {
                    if let RigidHead::Ctor(name, _) = head_copy {
                        if Some(name) == self.ctx.export_file.name_cache.nat_succ {
                            let new_spine = value::spine_snoc(self.arena, spine, Elim::app(a));
                            return self.try_fire_rigid(depth, head_copy, new_spine);
                        }
                    }
                }
                self.neutral_app(f, a)
            }
            Value::Unfold {
                head,
                spine,
                head_value,
                ..
            } => {
                let head = *head;
                let head_value = *head_value;
                let spine = *spine;
                if self.nat_extension && head.name.as_ref().is_nat_red() {
                    let new_spine = self.spine_snoc_hc(spine, Elim::app(a));
                    if let Some(args) = self.spine_apps(depth, new_spine) {
                        if let Some(r) = self.do_nat_red_shallow(depth, head.name, &args) {
                            return r;
                        }
                    }
                    return self.mk_unfold_hc(head.name, head.levels, new_spine, head_value);
                }
                self.neutral_app(f, a)
            }
            _ => panic!("apply: ill-typed application"),
        }
    }

    pub(crate) fn apply_many(&mut self, depth: u32, f0: V<'t>, args: &[V<'t>]) -> V<'t> {
        let mut f = f0;
        let mut i = 0usize;
        while i < args.len() {
            let Value::Lam { body: clo, .. } = f else {
                f = self.apply(depth, f, args[i]);
                i += 1;
                continue;
            };
            let mut env = self.env_extend(clo.env, args[i]);
            let mut body = clo.body;
            i += 1;
            while i < args.len() {
                let Expr::Lambda { body: inner, .. } = self.ctx.read_expr(body) else {
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
        clo: &Closure<'t>,
        v: V<'t>,
        binder_ty: Option<V<'t>>,
    ) -> V<'t> {
        let env = self.env_extend(clo.env, v);
        match clo.ctx {
            None => self.eval(depth, env, clo.body),
            Some(clo_ctx) => {
                let ty = binder_ty.expect("apply_closure: infer closure without a binder type");
                let ctx = value::ctx_extend(self.arena, clo_ctx, ty);
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

    fn try_fire_rigid(&mut self, depth: u32, head: RigidHead<'t>, spine: S<'t>) -> V<'t> {
        if self.ctx.export_file.config.nat_extension {
            if let RigidHead::Ctor(name, _) = head {
                if Some(name) == self.ctx.export_file.name_cache.nat_succ {
                    if let Spine::Snoc {
                        prev: Spine::Empty,
                        elim,
                        ..
                    } = spine
                    {
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

    fn nat_red_defer(&mut self, depth: u32, name: NamePtr<'t>, args: &[V<'t>]) -> bool {
        use crate::term::name::NatRed::*;
        let structural_on_second = matches!(name.as_ref().nat_red(), Some(Add | Sub | Mul | Pow));
        if !structural_on_second || args.len() != 2 {
            return false;
        }
        if let Value::NatLit { ptr, .. } = self.force_thunk(depth, args[1]) {
            self.ctx
                .read_bignum(*ptr)
                .map(|n| n.bits() > 8)
                .unwrap_or(false)
        } else {
            false
        }
    }

    pub(crate) fn value_type(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        let v = self.force_thunk(depth, v);
        match v {
            Value::Sort { level, .. } => {
                let s = self.ctx.succ(*level);
                value::mk_sort(self.arena, self.ctx.simplify(s))
            }
            Value::NatLit { .. } => {
                let n = self
                    .ctx
                    .export_file
                    .name_cache
                    .nat
                    .expect("value_type: Nat name missing");
                let levels = self.ctx.alloc_levels_slice(&[]);
                value::mk_rigid_head_with_empty(
                    self.arena,
                    RigidHead::Inductive(n, levels),
                    self.empty_spine(),
                )
            }
            Value::StrLit { .. } => {
                let n = self
                    .ctx
                    .export_file
                    .name_cache
                    .string
                    .expect("value_type: String name missing");
                let levels = self.ctx.alloc_levels_slice(&[]);
                value::mk_rigid_head_with_empty(
                    self.arena,
                    RigidHead::Inductive(n, levels),
                    self.empty_spine(),
                )
            }
            Value::Rigid { head, spine, .. } => {
                let head_ty = self.rigid_head_type(depth, *head);
                let prev = value::mk_rigid_head_with_empty(self.arena, *head, self.empty_spine());
                self.spine_type_with_value(depth, head_ty, prev, spine)
            }
            Value::Unfold { head, spine, .. } => {
                let head_ty = self.const_head_type(head.name, head.levels);
                let cell = &*self.arena.alloc(OnceCell::new());
                let _ = cell.set(head_ty);
                let prev = value::mk_unfold_head_with_empty(
                    self.arena,
                    head.name,
                    head.levels,
                    cell,
                    self.empty_spine(),
                );
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

    fn spine_type_with_value(
        &mut self,
        depth: u32,
        mut ty: V<'t>,
        prev_head: V<'t>,
        spine: S<'t>,
    ) -> V<'t> {
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
                    ty = self
                        .proj_field_type_with(depth, prev, ty, ty_name, idx)
                        .expect("spine_type_with_value: bad proj");
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
}
