use crate::env::{ConstructorData, Declar, RecursorData};
use crate::expr::{BinderStyle, Expr};
use crate::tc::{NatBinOp, TypeChecker};
use crate::util::{
    nat_div, nat_gcd, nat_land, nat_lor, nat_mod, nat_shl, nat_shr, nat_sub, nat_xor, BigUintPtr, ExprPtr, LevelPtr,
    LevelsPtr, NamePtr, StringPtr,
};
use crate::value::{self, Closure, Elim, RigidHead, Spine, Value, E, S, V};
use num_bigint::BigUint;
use num_traits::pow::Pow;
use std::cell::OnceCell;

#[inline]
fn rigid_head_key<'a>(head: &RigidHead<'a>) -> (u8, u64, u64) {
    match *head {
        RigidHead::BVar(lvl, ty) => (0, u64::from(lvl), ty as *const Value<'a> as u64),
        RigidHead::Local(e) => (1, e.get_hash(), 0),
        RigidHead::Axiom(n, l) => (2, n.get_hash(), l.get_hash()),
        RigidHead::Ctor(n, l) => (3, n.get_hash(), l.get_hash()),
        RigidHead::Recursor(n, l) => (4, n.get_hash(), l.get_hash()),
        RigidHead::QuotConst(n, l) => (5, n.get_hash(), l.get_hash()),
        RigidHead::Inductive(n, l) => (6, n.get_hash(), l.get_hash()),
    }
}

#[inline]
fn elim_key<'a>(elim: &Elim<'a>) -> (u8, u64, u64) {
    match *elim {
        Elim::App(v) => (0, v as *const Value<'a> as u64, 0),
        Elim::Proj { ty_name, idx } => (1, ty_name.get_hash(), idx as u64),
    }
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
        let key = (name, levels, spine as *const Spine<'t> as usize, head_value as *const OnceCell<V<'t>> as usize);
        if let Some(u) = self.tc_cache.unfold_hc.get(&key) {
            return u;
        }
        let u = value::mk_unfold(self.arena, name, levels, spine, head_value);
        self.tc_cache.unfold_hc.insert(key, u);
        u
    }

    fn env_extend_hc(&mut self, parent: E<'t>, v: V<'t>) -> E<'t> {
        let key = (parent as *const value::Env<'t> as usize, v as *const Value<'t> as usize);
        if let Some(e) = self.tc_cache.env_hc.get(&key) {
            return e;
        }
        let e = value::env_extend(self.arena, parent, v);
        self.tc_cache.env_hc.insert(key, e);
        e
    }

    #[inline]
    fn spine_snoc_hc(&mut self, prev: S<'t>, elim: Elim<'t>) -> S<'t> {
        let ek = elim_key(&elim);
        let key = (prev as *const Spine<'t> as usize, ek.0, ek.1, ek.2);
        if let Some(s) = self.tc_cache.spine_hc.get(&key) {
            return s;
        }
        let s = value::spine_snoc(self.arena, prev, elim);
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
        self.tc_cache.rigid_hc.insert(key, v);
        v
    }

    #[inline]
    fn mk_lam_hc(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        env: E<'t>,
        body_expr: ExprPtr<'t>,
    ) -> V<'t> {
        let key = (binder_type, env as *const value::Env<'t> as usize, body_expr);
        if let Some(v) = self.tc_cache.lam_hc.get(&key) {
            return v;
        }
        let v = value::mk_lam(self.arena, binder_name, binder_style, binder_type, Closure { env, body: body_expr });
        self.tc_cache.lam_hc.insert(key, v);
        v
    }

    #[inline]
    fn canonicalize_for_spine(&mut self, v: V<'t>) -> V<'t> {
        if matches!(v, Value::Thunk { .. }) {
            return v;
        }
        let key = v as *const Value<'t> as usize;
        if let Some(c) = self.tc_cache.canon_cache.get(&key) {
            return c;
        }
        let c = self.canon_compute(v);
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
            Spine::Snoc(prev, elim) => {
                let cprev = self.canon_spine(prev);
                let celim = match elim {
                    Elim::App(a) => {
                        let ca = self.canonicalize_for_spine(a);
                        Elim::App(ca)
                    }
                    Elim::Proj { ty_name, idx } => Elim::Proj { ty_name: *ty_name, idx: *idx },
                };
                self.spine_snoc_hc(cprev, celim)
            }
        }
    }

    fn canon_compute(&mut self, v: V<'t>) -> V<'t> {
        match v {
            Value::Lam { binder_name, binder_style, binder_type, body, .. } =>
                self.mk_lam_hc(*binder_name, *binder_style, *binder_type, body.env, body.body),
            Value::Pi { binder_name, binder_style, domain, body } =>
                self.mk_pi_hc(*binder_name, *binder_style, domain, body.env, body.body),
            Value::Sort { level } => self.canon_content(0, level.get_hash(), v),
            Value::NatLit { ptr } => self.canon_content(1, ptr.get_hash(), v),
            Value::StrLit { ptr } => self.canon_content(2, ptr.get_hash(), v),
            Value::Rigid { head, spine } => {
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
        env: E<'t>,
        body_expr: ExprPtr<'t>,
    ) -> V<'t> {
        let key = (domain as *const Value<'t> as usize, env as *const value::Env<'t> as usize, body_expr);
        if let Some(v) = self.tc_cache.pi_hc.get(&key) {
            return v;
        }
        let v = value::mk_pi(self.arena, binder_name, binder_style, domain, Closure { env, body: body_expr });
        self.tc_cache.pi_hc.insert(key, v);
        v
    }
}

impl<'x, 't, 'p> TypeChecker<'x, 't, 'p> {
    pub(crate) fn eval(&mut self, env: E<'t>, e: ExprPtr<'t>) -> V<'t> {
        let first = self.ctx.read_expr_ref(e);
        if matches!(
            first,
            Expr::App { num_loose_bvars: 0, .. }
                | Expr::Pi { num_loose_bvars: 0, .. }
                | Expr::Lambda { num_loose_bvars: 0, .. }
                | Expr::Let { num_loose_bvars: 0, .. }
                | Expr::Proj { num_loose_bvars: 0, .. }
        ) {
            if let Some(v) = self.tc_cache.closed_eval_cache.get(&e) {
                return v;
            }
            let v = self.eval_no_cache(env, e);
            self.tc_cache.closed_eval_cache.insert(e, v);
            return v;
        }
        if matches!(
            first,
            Expr::App { .. } | Expr::Proj { .. } | Expr::Let { .. } | Expr::Pi { .. } | Expr::Lambda { .. }
        ) {
            let key = (env as *const value::Env<'t> as usize, e);
            if let Some(v) = self.tc_cache.open_eval_cache.get(&key) {
                return v;
            }
            let v = self.eval_no_cache(env, e);
            if !self.tc_cache.open_eval_seen.insert(e) {
                self.tc_cache.open_eval_cache.insert(key, v);
            }
            return v;
        }
        self.eval_no_cache(env, e)
    }

    fn eval_no_cache(&mut self, env: E<'t>, e: ExprPtr<'t>) -> V<'t> {
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
                let mut result = self.eval(env, leaf_expr);
                let nat_ext = self.nat_extension;

                if all_same {
                    let f_val = match self.ctx.read_expr_ref(first_fun) {
                        &Expr::Var { dbj_idx, .. } => {
                            let v = env.lookup(dbj_idx).expect("eval: loose bvar");
                            self.force_thunk(v)
                        }
                        _ => self.eval(env, first_fun),
                    };
                    if let Value::Rigid { head, spine } = f_val {
                        let head_copy = *head;
                        let head_spine = *spine;
                        let is_nat_ctor = nat_ext && matches!(head_copy, RigidHead::Ctor(_, _));
                        if !is_nat_ctor {
                            for _ in 0..count {
                                let a = self.canonicalize_for_spine(result);
                                let ns = self.spine_snoc_hc(head_spine, Elim::App(a));
                                result = self.mk_rigid_hc(head_copy, ns);
                            }
                            return result;
                        }
                    }
                    for _ in 0..count {
                        result = self.apply(f_val, result);
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
                                self.force_thunk(v)
                            }
                            _ => self.eval(env, f_expr),
                        };
                        last_f_expr = Some(f_expr);
                        last_f_val = Some(v);
                        v
                    };
                    if let Value::Rigid { head, spine } = f_val {
                        let head_copy = *head;
                        let is_nat_ctor = nat_ext && matches!(head_copy, RigidHead::Ctor(_, _));
                        if !is_nat_ctor {
                            let sp = *spine;
                            let a = self.canonicalize_for_spine(result);
                            let ns = self.spine_snoc_hc(sp, Elim::App(a));
                            result = self.mk_rigid_hc(head_copy, ns);
                            continue;
                        }
                    }
                    result = self.apply(f_val, result);
                }
                return result;
            }
            let f = self.eval(env, fun);
            let trivial = matches!(
                self.ctx.read_expr_ref(arg),
                Expr::Var { .. }
                    | Expr::Sort { .. }
                    | Expr::Const { .. }
                    | Expr::NatLit { .. }
                    | Expr::StringLit { .. }
                    | Expr::Local { .. }
            );
            if let Value::Lam { body: clo, .. } = f {
                let a = if trivial { self.eval(env, arg) } else { value::mk_thunk(self.arena, env, arg) };
                let clo_env = clo.env;
                let clo_body = clo.body;
                let new_env = self.env_extend_hc(clo_env, a);
                return self.eval(new_env, clo_body);
            }
            let a = if trivial { self.eval(env, arg) } else { value::mk_thunk(self.arena, env, arg) };
            return self.apply(f, a);
        }
        match first {
            Expr::Var { dbj_idx, .. } => {
                let v = env.lookup(dbj_idx).expect("eval: loose bvar");
                self.force_thunk(v)
            }
            Expr::Sort { level, .. } => value::mk_sort(self.arena, self.ctx.simplify(level)),
            Expr::Const { name, levels, .. } => self.eval_const(name, levels),
            Expr::App { .. } => unreachable!(),
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } =>
                value::mk_lam(self.arena, binder_name, binder_style, binder_type, Closure { env, body }),
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                let dom = match self.ctx.read_expr_ref(binder_type) {
                    Expr::Var { .. }
                    | Expr::Sort { .. }
                    | Expr::Const { .. }
                    | Expr::NatLit { .. }
                    | Expr::StringLit { .. }
                    | Expr::Local { .. } => self.eval(env, binder_type),
                    _ => value::mk_thunk(self.arena, env, binder_type),
                };
                value::mk_pi(self.arena, binder_name, binder_style, dom, Closure { env, body })
            }
            Expr::Let { .. } => {
                let mut env = env;
                let mut cursor = e;
                while let Expr::Let { val, body, .. } = self.ctx.read_expr(cursor) {
                    let vv = self.eval(env, val);
                    env = self.env_extend_hc(env, vv);
                    cursor = body;
                }
                self.eval(env, cursor)
            }
            Expr::Local { .. } => {
                let idx = e.idx();
                if idx < self.local_v_cache.len() {
                    if let Some(v) = self.local_v_cache[idx] {
                        return v;
                    }
                }
                let empty = self.empty_spine();
                let v = value::mk_local_with_empty(self.arena, e, empty);
                if idx >= self.local_v_cache.len() {
                    self.local_v_cache.resize(idx + 1, None);
                }
                self.local_v_cache[idx] = Some(v);
                v
            }
            Expr::Proj { ty_name, idx, structure, .. } => {
                let vs = self.eval(env, structure);
                self.do_proj(ty_name, idx, vs)
            }
            Expr::NatLit { ptr, .. } => value::mk_natlit(self.arena, ptr),
            Expr::StringLit { ptr, .. } => value::mk_strlit(self.arena, ptr),
        }
    }

    pub(crate) fn eval_const(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> V<'t> {
        if let Some(cached) = self.tc_cache.const_head_value_cache.get(&(name, levels)) {
            return cached;
        }
        let empty = self.empty_spine();
        let v = match self.env.get_declar(&name) {
            Some(Declar::Definition { .. }) | Some(Declar::Theorem { .. }) => {
                let cell = &*self.arena.alloc(OnceCell::new());
                value::mk_unfold_head_with_empty(self.arena, name, levels, cell, empty)
            }
            Some(Declar::Constructor(_)) =>
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Ctor(name, levels), empty),
            Some(Declar::Recursor(_)) =>
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Recursor(name, levels), empty),
            Some(Declar::Quot { .. }) =>
                value::mk_rigid_head_with_empty(self.arena, RigidHead::QuotConst(name, levels), empty),
            Some(Declar::Inductive(_)) =>
                value::mk_rigid_head_with_empty(self.arena, RigidHead::Inductive(name, levels), empty),
            Some(Declar::Axiom { .. }) | Some(Declar::Opaque { .. }) | None =>
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
        loop {
            let cur_f = self.force_all(cur);
            match cur_f {
                Value::Pi { domain, body, .. } => {
                    let fresh = self.mk_bvar_hc(0, domain);
                    let body = Closure { env: body.env, body: body.body };
                    cur = self.apply_closure_v(&body, fresh);
                }
                Value::Sort { level } => {
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
        let ty_e = self.ctx.subst_expr_levels(info.ty, info.uparams, levels);
        let empty = self.empty_env();
        let v = self.eval(empty, ty_e);
        self.tc_cache.const_head_type_cache.insert((name, levels), v);
        v
    }

    #[inline]
    pub(crate) fn force_thunk(&mut self, v: V<'t>) -> V<'t> {
        if let Value::Thunk { env, expr, forced } = v {
            if let Some(r) = forced.get() {
                return r;
            }
            let r = self.eval(env, *expr);
            let _ = forced.set(r);
            return r;
        }
        v
    }

    pub(crate) fn lam_domain(&mut self, v: V<'t>) -> V<'t> {
        match v {
            Value::Lam { binder_type, domain, body, .. } => {
                if let Some(d) = domain.get() {
                    return d;
                }
                let e = body.env;
                let bt = *binder_type;
                let d = self.eval(e, bt);
                let _ = domain.set(d);
                d
            }
            Value::Pi { domain, .. } => domain,
            _ => panic!("lam_domain: not a Lam/Pi"),
        }
    }

    #[inline]
    pub(crate) fn apply(&mut self, f: V<'t>, a: V<'t>) -> V<'t> {
        match f {
            Value::Lam { body: clo, .. } => {
                let clo_env = clo.env;
                let clo_body = clo.body;
                let env = self.env_extend_hc(clo_env, a);
                self.eval(env, clo_body)
            }
            Value::Rigid { head, spine } => {
                let head_copy = *head;
                if self.nat_extension {
                    if let RigidHead::Ctor(name, _) = head_copy {
                        if Some(name) == self.ctx.export_file.name_cache.nat_succ {
                            let new_spine = value::spine_snoc(self.arena, spine, Elim::App(a));
                            return self.try_fire_rigid(head_copy, new_spine);
                        }
                    }
                }
                let a = self.canonicalize_for_spine(a);
                let new_spine = self.spine_snoc_hc(spine, Elim::App(a));
                self.mk_rigid_hc(head_copy, new_spine)
            }
            Value::Unfold { head, spine, head_value, .. } => {
                let head = *head;
                let head_value = *head_value;
                let spine = *spine;
                if self.nat_extension && self.is_nat_red_name(head.name) {
                    let new_spine = self.spine_snoc_hc(spine, Elim::App(a));
                    if let Some(args) = self.spine_apps(new_spine) {
                        if let Some(r) = self.do_nat_red_shallow(head.name, &args) {
                            return r;
                        }
                    }
                    return self.mk_unfold_hc(head.name, head.levels, new_spine, head_value);
                }
                let a = self.canonicalize_for_spine(a);
                let new_spine = self.spine_snoc_hc(spine, Elim::App(a));
                self.mk_unfold_hc(head.name, head.levels, new_spine, head_value)
            }
            _ => panic!("apply: ill-typed application"),
        }
    }

    pub(crate) fn apply_v(&mut self, f: V<'t>, a: V<'t>) -> V<'t> { self.apply(f, a) }

    pub(crate) fn apply_closure(&mut self, clo: &Closure<'t>, v: V<'t>) -> V<'t> {
        let clo_env = clo.env;
        let clo_body = clo.body;
        let env = self.env_extend_hc(clo_env, v);
        self.eval(env, clo_body)
    }

    pub(crate) fn apply_closure_v(&mut self, clo: &Closure<'t>, v: V<'t>) -> V<'t> { self.apply_closure(clo, v) }

    fn try_fire_rigid(&mut self, head: RigidHead<'t>, spine: S<'t>) -> V<'t> {
        if self.ctx.export_file.config.nat_extension {
            if let RigidHead::Ctor(name, _) = head {
                if Some(name) == self.ctx.export_file.name_cache.nat_succ {
                    if let Spine::Snoc(Spine::Empty, Elim::App(arg)) = spine {
                        if let Some(n) = self.value_to_bignum_at(arg, false) {
                            let succ_lit = n + 1u8;
                            if let Some(p) = self.ctx.alloc_bignum(succ_lit) {
                                return value::mk_natlit(self.arena, p);
                            }
                        }
                    }
                }
            }
        }
        self.mk_rigid_hc(head, spine)
    }

    fn is_nat_red_name(&self, name: NamePtr<'t>) -> bool {
        let nc = &self.ctx.export_file.name_cache;
        Some(name) == nc.nat_succ
            || Some(name) == nc.nat_add
            || Some(name) == nc.nat_sub
            || Some(name) == nc.nat_mul
            || Some(name) == nc.nat_pow
            || Some(name) == nc.nat_mod
            || Some(name) == nc.nat_div
            || Some(name) == nc.nat_beq
            || Some(name) == nc.nat_ble
            || Some(name) == nc.nat_land
            || Some(name) == nc.nat_lor
            || Some(name) == nc.nat_xor
            || Some(name) == nc.nat_gcd
            || Some(name) == nc.nat_shl
            || Some(name) == nc.nat_shr
            || Some(name) == nc.nat_div_go
            || Some(name) == nc.nat_mod_core_go
    }

    fn nat_red_defer(&mut self, name: NamePtr<'t>, args: &[V<'t>]) -> bool {
        let nc = &self.ctx.export_file.name_cache;
        let structural_on_second = Some(name) == nc.nat_add
            || Some(name) == nc.nat_sub
            || Some(name) == nc.nat_mul
            || Some(name) == nc.nat_pow;
        if !structural_on_second || args.len() != 2 {
            return false;
        }
        if let Value::NatLit { ptr } = self.force_thunk(args[1]) {
            self.ctx.read_bignum(*ptr).map(|n| n.bits() > 8).unwrap_or(false)
        } else {
            false
        }
    }

    pub(crate) fn value_type(&mut self, v: V<'t>) -> V<'t> {
        let v = self.force_thunk(v);
        match v {
            Value::Sort { level } => {
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
            Value::Rigid { head, spine } => {
                let head_ty = self.rigid_head_type(*head);
                self.spine_type(head_ty, *head, spine)
            }
            Value::Unfold { head, spine, .. } => {
                let head_ty = self.const_head_type(head.name, head.levels);
                let cell = &*self.arena.alloc(OnceCell::new());
                let _ = cell.set(head_ty);
                let prev =
                    value::mk_unfold_head_with_empty(self.arena, head.name, head.levels, cell, self.empty_spine());
                self.spine_type_with_value(head_ty, prev, spine)
            }
            Value::Pi { .. } | Value::Lam { .. } => panic!("value_type: Pi/Lam not supported"),
            Value::Thunk { .. } => unreachable!("value_type: Thunk after force"),
        }
    }

    fn rigid_head_type(&mut self, head: RigidHead<'t>) -> V<'t> {
        match head {
            RigidHead::BVar(_, ty) => ty,
            RigidHead::Local(e) => {
                let bt = match self.ctx.read_expr(e) {
                    Expr::Local { binder_type, .. } => binder_type,
                    _ => panic!("value_type: Local Expr"),
                };
                let empty = self.empty_env();
                self.eval(empty, bt)
            }
            RigidHead::Axiom(n, ls)
            | RigidHead::Ctor(n, ls)
            | RigidHead::Recursor(n, ls)
            | RigidHead::QuotConst(n, ls)
            | RigidHead::Inductive(n, ls) => self.const_head_type(n, ls),
        }
    }

    fn spine_type(&mut self, mut ty: V<'t>, head: RigidHead<'t>, spine: S<'t>) -> V<'t> {
        let mut prefix = value::spine_empty(self.arena);
        for elim in spine.to_vec() {
            match elim {
                Elim::App(a) => {
                    let ty_f = self.force_all(ty);
                    match ty_f {
                        Value::Pi { body, .. } => {
                            let body = Closure { env: body.env, body: body.body };
                            ty = self.apply_closure(&body, a);
                        }
                        _ => panic!("spine_type: expected Pi"),
                    }
                    prefix = value::spine_snoc(self.arena, prefix, Elim::App(a));
                }
                Elim::Proj { ty_name, idx } => {
                    let prev = value::mk_rigid(self.arena, head, prefix);
                    ty = self.proj_field_type_with(prev, ty, *ty_name, *idx).expect("spine_type: bad proj");
                    prefix = value::spine_snoc(self.arena, prefix, Elim::Proj { ty_name: *ty_name, idx: *idx });
                }
            }
        }
        ty
    }

    fn spine_type_with_value(&mut self, mut ty: V<'t>, prev_head: V<'t>, spine: S<'t>) -> V<'t> {
        let mut prev = prev_head;
        for elim in spine.to_vec() {
            match elim {
                Elim::App(a) => {
                    let ty_f = self.force_all(ty);
                    match ty_f {
                        Value::Pi { body, .. } => {
                            let body = Closure { env: body.env, body: body.body };
                            ty = self.apply_closure(&body, a);
                        }
                        _ => panic!("spine_type_with_value: expected Pi"),
                    }
                    prev = self.apply(prev, a);
                }
                Elim::Proj { ty_name, idx } => {
                    ty = self.proj_field_type_with(prev, ty, *ty_name, *idx).expect("spine_type_with_value: bad proj");
                    prev = self.do_proj(*ty_name, *idx, prev);
                }
            }
        }
        ty
    }

    pub(crate) fn whnf_head(&mut self, v: V<'t>) -> V<'t> {
        let mut cur = v;
        loop {
            cur = self.force_thunk(cur);
            match cur {
                Value::Unfold { .. } => {
                    let next = self.unfold_value(cur);
                    if std::ptr::eq(next, cur) {
                        return cur;
                    }
                    cur = next;
                }
                Value::Rigid { head: RigidHead::Recursor(..) | RigidHead::QuotConst(..), .. } =>
                    match self.iota_value(cur) {
                        Some(next) => cur = next,
                        None => return cur,
                    },
                _ => return cur,
            }
        }
    }

    pub(crate) fn do_proj(&mut self, ty_name: NamePtr<'t>, idx: usize, v: V<'t>) -> V<'t> {
        let v = self.whnf_head(v);
        match v {
            Value::Rigid { head: RigidHead::Ctor(ctor_name, _), spine, .. } => {
                if let Some(ConstructorData { num_params, inductive_name, .. }) = self.env.get_constructor(ctor_name) {
                    if *inductive_name == ty_name {
                        let np = usize::from(*num_params);
                        if let Some(Elim::App(field)) = spine.get(np + idx) {
                            return self.force_thunk(field);
                        }
                    }
                }
                self.proj_extend_spine(ty_name, idx, v)
            }
            Value::NatLit { ptr } => {
                let ctor = self.nat_lit_to_ctor_val(*ptr).expect("do_proj: nat_lit_to_ctor_val failed");
                self.do_proj(ty_name, idx, ctor)
            }
            Value::StrLit { ptr } => {
                let ctor = self.str_lit_to_ctor_val(*ptr).expect("do_proj: str_lit_to_ctor_val failed");
                self.do_proj(ty_name, idx, ctor)
            }
            Value::Rigid { .. } | Value::Unfold { .. } => self.proj_extend_spine(ty_name, idx, v),
            Value::Thunk { .. } => unreachable!("do_proj: Thunk after force_all"),
            _ => panic!("do_proj: not a neutral"),
        }
    }

    fn proj_extend_spine(&mut self, ty_name: NamePtr<'t>, idx: usize, v: V<'t>) -> V<'t> {
        match v {
            Value::Rigid { head, spine } => {
                let (h, sp) = (*head, *spine);
                let ns = self.spine_snoc_hc(sp, Elim::Proj { ty_name, idx });
                self.mk_rigid_hc(h, ns)
            }
            Value::Unfold { head, spine, head_value, .. } => {
                let (hn, hl, hv, sp) = (head.name, head.levels, *head_value, *spine);
                let ns = self.spine_snoc_hc(sp, Elim::Proj { ty_name, idx });
                self.mk_unfold_hc(hn, hl, ns, hv)
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn proj_field_type_with(
        &mut self,
        struct_value: V<'t>,
        struct_ty: V<'t>,
        ty_name: NamePtr<'t>,
        idx: usize,
    ) -> Option<V<'t>> {
        let struct_ty = self.force_all(struct_ty);
        let (ind_name, ind_levels, args) = match struct_ty {
            Value::Rigid { head: RigidHead::Inductive(n, ls), spine, .. } => {
                let aa = self.spine_apps(spine)?;
                (*n, *ls, aa)
            }
            _ => return None,
        };
        if ind_name != ty_name {
            return None;
        }
        let ind = self.env.get_inductive(&ind_name)?;
        let ctor_name = ind.all_ctor_names[0];
        let ctor_info = match self.env.get_declar(&ctor_name)? {
            Declar::Constructor(c) => c.info,
            _ => return None,
        };
        let ctor_ty_e = self.ctx.subst_expr_levels(ctor_info.ty, ctor_info.uparams, ind_levels);
        let mut cur = {
            let empty = self.empty_env();
            self.eval(empty, ctor_ty_e)
        };
        let num_params = usize::from(ind.num_params);
        for i in 0..num_params {
            let cf = self.force_all(cur);
            match cf {
                Value::Pi { body, .. } => {
                    let body = Closure { env: body.env, body: body.body };
                    let arg = *args.get(i)?;
                    cur = self.apply_closure_v(&body, arg);
                }
                _ => return None,
            }
        }
        for i in 0..idx {
            let cf = self.force_all(cur);
            match cf {
                Value::Pi { body, .. } => {
                    let body = Closure { env: body.env, body: body.body };
                    let prior = self.do_proj(ty_name, i, struct_value);
                    cur = self.apply_closure_v(&body, prior);
                }
                _ => return None,
            }
        }
        let cf = self.force_all(cur);
        match cf {
            Value::Pi { domain, .. } => Some(*domain),
            _ => None,
        }
    }

    pub(crate) fn force_all(&mut self, v: V<'t>) -> V<'t> {
        let mut cur = v;
        let mut waiting: Vec<V<'t>> = Vec::new();
        loop {
            loop {
                match cur {
                    Value::Thunk { .. } => cur = self.force_thunk(cur),
                    Value::Unfold { .. } => {
                        let next = self.unfold_value(cur);
                        if std::ptr::eq(next, cur) {
                            break;
                        }
                        cur = next;
                    }
                    _ => break,
                }
            }
            let step = match cur {
                Value::Rigid { head: RigidHead::Recursor(..) | RigidHead::QuotConst(..), .. } => self.iota_step(cur),
                _ => ForceStep::Done,
            };
            match step {
                ForceStep::Reduced(next) => {
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
                    None => return cur,
                    Some(rec_val) => {
                        let key = rec_val as *const Value<'t> as usize;
                        match self.fire_value(rec_val, cur) {
                            Some(res) => {
                                self.tc_cache.iota_cache.insert(key, res);
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
        }
    }

    fn iota_step(&mut self, v: V<'t>) -> ForceStep<'t> {
        let key = v as *const Value<'t> as usize;
        if self.tc_cache.iota_stuck.contains(&key) {
            return ForceStep::Done;
        }
        if let Some(c) = self.tc_cache.iota_cache.get(&key) {
            return ForceStep::Reduced(c);
        }
        match v {
            Value::Rigid { head: RigidHead::Recursor(name, levels), spine } => {
                let env = self.env;
                let rec = match env.get_recursor(name) {
                    Some(r) => r,
                    None => return ForceStep::Done,
                };
                let args = match self.spine_apps(spine) {
                    Some(a) => a,
                    None => return ForceStep::Done,
                };
                if args.len() <= rec.major_idx() {
                    return ForceStep::Done;
                }
                if let Some(r) = self.k_pre_reduce(&rec, *levels, &args) {
                    self.tc_cache.iota_cache.insert(key, r);
                    return ForceStep::Reduced(r);
                }
                let major_h = self.strip_head(args[rec.major_idx()]);
                if self.is_iota_reducible(major_h) {
                    return ForceStep::Descend(major_h);
                }
                match self.fire_recursor(&rec, *levels, &args, major_h) {
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
            Value::Rigid { head: RigidHead::QuotConst(name, _), spine } => {
                let cache = self.ctx.export_file.name_cache;
                let qmk_pos = if Some(*name) == cache.quot_lift {
                    5
                } else if Some(*name) == cache.quot_ind {
                    4
                } else {
                    return ForceStep::Done;
                };
                let name = *name;
                let args = match self.spine_apps(spine) {
                    Some(a) => a,
                    None => return ForceStep::Done,
                };
                let major = match args.get(qmk_pos) {
                    Some(m) => *m,
                    None => return ForceStep::Done,
                };
                let major_h = self.strip_head(major);
                if self.is_iota_reducible(major_h) {
                    return ForceStep::Descend(major_h);
                }
                match self.fire_quot(name, &args, major_h) {
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

    fn strip_head(&mut self, v: V<'t>) -> V<'t> {
        let mut cur = v;
        loop {
            match cur {
                Value::Thunk { .. } => cur = self.force_thunk(cur),
                Value::Unfold { .. } => {
                    let next = self.unfold_value(cur);
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

    fn fire_value(&mut self, rec_val: V<'t>, major: V<'t>) -> Option<V<'t>> {
        match rec_val {
            Value::Rigid { head: RigidHead::Recursor(name, levels), spine } => {
                let env = self.env;
                let rec = env.get_recursor(name)?;
                let args = self.spine_apps(spine)?;
                if args.len() <= rec.major_idx() {
                    return None;
                }
                self.fire_recursor(&rec, *levels, &args, major)
            }
            Value::Rigid { head: RigidHead::QuotConst(name, _), spine } => {
                let args = self.spine_apps(spine)?;
                self.fire_quot(*name, &args, major)
            }
            _ => None,
        }
    }

    pub(crate) fn unfold_value(&mut self, v: V<'t>) -> V<'t> { self.unfold_value_go(v, false) }

    pub(crate) fn unfold_value_demand(&mut self, v: V<'t>) -> V<'t> {
        self.unfold_value_go(v, self.tc_cache.probe_depth == 0)
    }

    fn unfold_value_go(&mut self, v: V<'t>, force: bool) -> V<'t> {
        if let Value::Unfold { head, spine, head_value, forced } = v {
            if let Some(f) = forced.get() {
                return f;
            }
            if self.nat_extension && self.is_nat_red_name(head.name) {
                if let Some(args) = self.spine_apps(spine) {
                    if let Some(r) = self.do_nat_red(head.name, &args) {
                        let _ = forced.set(r);
                        return r;
                    }
                    if !force && self.nat_red_defer(head.name, &args) {
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
            for e in spine.to_vec() {
                cur = match e {
                    Elim::App(a) => self.apply(cur, a),
                    Elim::Proj { ty_name, idx } => self.do_proj(*ty_name, *idx, cur),
                };
            }
            let _ = forced.set(cur);
            return cur;
        }
        v
    }

    pub(crate) fn iota_value(&mut self, v: V<'t>) -> Option<V<'t>> {
        let v_key = v as *const Value<'t> as usize;
        if self.tc_cache.iota_stuck.contains(&v_key) {
            return None;
        }
        if let Some(cached) = self.tc_cache.iota_cache.get(&v_key) {
            return Some(*cached);
        }
        let result = match v {
            Value::Rigid { head: RigidHead::Recursor(name, levels), spine, .. } => {
                let args = self.spine_apps(spine)?;
                self.do_recursor_iota(*name, *levels, &args)
            }
            Value::Rigid { head: RigidHead::QuotConst(name, _), spine, .. } => {
                let args = self.spine_apps(spine)?;
                self.do_quot_iota(*name, &args)
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
        let (def_uparams, def_value) = self.env.get_declar_val(&name)?;
        if self.ctx.read_levels(levels).len() != self.ctx.read_levels(def_uparams).len() {
            return None;
        }
        let body = self.ctx.subst_expr_levels(def_value, def_uparams, levels);
        let empty = self.empty_env();
        let v = self.eval(empty, body);
        self.tc_cache.unfold_const_cache.insert((name, levels), v);
        Some(v)
    }

    pub(crate) fn spine_apps(&mut self, spine: S<'t>) -> Option<Vec<V<'t>>> {
        let mut out = Vec::with_capacity(spine.len() as usize);
        let mut cur: &Spine<'t> = spine;
        while let Spine::Snoc(prev, elim) = cur {
            match elim {
                Elim::App(a) => out.push(self.force_thunk(a)),
                Elim::Proj { .. } => return None,
            }
            cur = prev;
        }
        out.reverse();
        Some(out)
    }

    fn do_recursor_iota(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        let env = self.env;
        let rec = env.get_recursor(&name)?;
        if args.len() <= rec.major_idx() {
            return None;
        }
        if let Some(r) = self.k_pre_reduce(&rec, levels, args) {
            return Some(r);
        }
        let major = self.whnf_head(args[rec.major_idx()]);
        self.fire_recursor(&rec, levels, args, major)
    }

    fn k_pre_reduce(&mut self, rec: &RecursorData<'t>, levels: LevelsPtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        if !rec.is_k {
            return None;
        }
        let raw = self.force_thunk(args[rec.major_idx()]);
        let kctor = self.try_k_reduce(raw, rec)?;
        self.fire_recursor(rec, levels, args, kctor)
    }

    fn fire_recursor(
        &mut self,
        rec: &RecursorData<'t>,
        levels: LevelsPtr<'t>,
        args: &[V<'t>],
        major: V<'t>,
    ) -> Option<V<'t>> {
        if self.ctx.export_file.config.nat_extension
            && rec.all_inductives.first().copied() == self.ctx.export_file.name_cache.nat
        {
            if let Value::NatLit { ptr } = major {
                return Some(self.nat_rec_natlit(args, *ptr, rec, levels));
            }
        }
        let major = self
            .major_to_ctor(major)
            .or_else(|| self.try_k_reduce(major, rec))
            .or_else(|| self.try_struct_eta_reduce(major, rec))
            .unwrap_or(major);
        let (ctor_name, ctor_args) = self.unwrap_ctor_app(major)?;
        let rec_rule = rec.rec_rules.iter().find(|r| r.ctor_name == ctor_name).copied()?;
        let num_extra = ctor_args.len().checked_sub(usize::from(rec_rule.ctor_telescope_size_wo_params))?;
        let cache_key = (rec_rule.val, levels);
        let mut result = match self.tc_cache.rec_rule_cache.get(&cache_key) {
            Some(v) => *v,
            None => {
                let body = self.ctx.subst_expr_levels(rec_rule.val, rec.info.uparams, levels);
                let empty = self.empty_env();
                let v = self.eval(empty, body);
                self.tc_cache.rec_rule_cache.insert(cache_key, v);
                v
            }
        };
        let nprefix = usize::from(rec.num_params + rec.num_motives + rec.num_minors);
        for a in &args[..nprefix] {
            result = self.apply_v(result, a);
        }
        for a in &ctor_args[num_extra..] {
            result = self.apply_v(result, a);
        }
        for a in &args[rec.major_idx() + 1..] {
            result = self.apply_v(result, a);
        }
        Some(result)
    }

    fn nat_rec_natlit(
        &mut self,
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
        let succ_case = self.force_thunk(args[nparams + nmotives + 1]);
        let mut result = if n.is_zero() {
            zero_case
        } else {
            let pred = n - 1u8;
            let pred_ptr = self.ctx.alloc_bignum(pred).expect("nat_rec_natlit: alloc pred");
            let pred_val = value::mk_natlit(self.arena, pred_ptr);
            let empty = self.empty_spine();
            let mut ih = value::mk_rigid_head_with_empty(self.arena, RigidHead::Recursor(rec.info.name, levels), empty);
            for a in &args[..major_idx] {
                ih = self.apply_v(ih, a);
            }
            ih = self.apply_v(ih, pred_val);
            let stepped = self.apply_v(succ_case, pred_val);
            self.apply_v(stepped, ih)
        };
        for a in &args[major_idx + 1..] {
            result = self.apply_v(result, a);
        }
        result
    }

    fn try_struct_eta_reduce(&mut self, major: V<'t>, rec: &RecursorData<'t>) -> Option<V<'t>> {
        if !matches!(major, Value::Rigid { .. } | Value::Unfold { .. }) {
            return None;
        }
        let rec_induct = self.ctx.get_major_induct(rec)?;
        if !self.env.can_be_struct(&rec_induct) {
            return None;
        }
        let key = (major as *const Value<'t> as usize, rec_induct);
        if let Some(cached) = self.tc_cache.struct_eta_cache.get(&key) {
            return *cached;
        }
        let result = self.try_struct_eta_reduce_uncached(major, rec, rec_induct);
        self.tc_cache.struct_eta_cache.insert(key, result);
        result
    }

    fn try_struct_eta_reduce_uncached(
        &mut self,
        major: V<'t>,
        rec: &RecursorData<'t>,
        rec_induct: NamePtr<'t>,
    ) -> Option<V<'t>> {
        let major_ty = self.value_type(major);
        let major_ty_f = self.force_all(major_ty);
        let (ty_name, ty_levels, ty_args) = self.unwrap_inductive_app(major_ty_f)?;
        if ty_name != rec_induct {
            return None;
        }
        let ind = self.env.get_inductive(&ty_name)?;
        let ctor_name = ind.all_ctor_names[0];
        let ctor_data = self.env.get_constructor(&ctor_name)?;
        let num_fields = usize::from(ctor_data.num_fields);
        let np = usize::from(rec.num_params);
        let mut new_ctor =
            value::mk_rigid_head_with_empty(self.arena, RigidHead::Ctor(ctor_name, ty_levels), self.empty_spine());
        for a in ty_args.iter().take(np).copied() {
            new_ctor = self.apply_v(new_ctor, a);
        }
        for i in 0..num_fields {
            let proj = self.do_proj(ty_name, i, major);
            new_ctor = self.apply_v(new_ctor, proj);
        }
        Some(new_ctor)
    }

    fn try_k_reduce(&mut self, major: V<'t>, rec: &RecursorData<'t>) -> Option<V<'t>> {
        if !rec.is_k {
            return None;
        }
        if !matches!(major, Value::Rigid { .. } | Value::Unfold { .. }) {
            return None;
        }
        let major_ty = self.value_type(major);
        let major_ty_f = self.force_all(major_ty);
        let (ty_name, ty_levels, ty_args) = self.unwrap_inductive_app(major_ty_f)?;
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
            new_ctor = self.apply_v(new_ctor, a);
        }
        let new_ty = self.value_type(new_ctor);
        if !self.conv_types(major_ty_f, new_ty) {
            return None;
        }
        Some(new_ctor)
    }

    fn unwrap_inductive_app(&mut self, v: V<'t>) -> Option<(NamePtr<'t>, LevelsPtr<'t>, Vec<V<'t>>)> {
        match v {
            Value::Rigid { head: RigidHead::Inductive(n, ls), spine, .. } => {
                let args = self.spine_apps(spine)?;
                Some((*n, *ls, args))
            }
            _ => None,
        }
    }

    fn major_to_ctor(&mut self, major: V<'t>) -> Option<V<'t>> {
        match major {
            Value::NatLit { ptr } => self.nat_lit_to_ctor_val(*ptr),
            Value::StrLit { ptr } => self.str_lit_to_ctor_val(*ptr),
            _ => None,
        }
    }

    pub(crate) fn str_lit_to_ctor_val(&mut self, s: StringPtr<'t>) -> Option<V<'t>> {
        let ctor_expr = self.ctx.str_lit_to_constructor(s)?;
        let empty = self.empty_env();
        let v = self.eval(empty, ctor_expr);
        Some(self.whnf_head(v))
    }

    fn nat_lit_to_ctor_val(&mut self, n: BigUintPtr<'t>) -> Option<V<'t>> {
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
            Some(self.apply_v(succ_v, pred_v))
        }
    }

    fn unwrap_ctor_app(&mut self, v: V<'t>) -> Option<(NamePtr<'t>, Vec<V<'t>>)> {
        match v {
            Value::Rigid { head: RigidHead::Ctor(name, _), spine, .. } => {
                let args = self.spine_apps(spine)?;
                Some((*name, args))
            }
            _ => None,
        }
    }

    fn do_quot_iota(&mut self, c_name: NamePtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        let cache = self.ctx.export_file.name_cache;
        let qmk_pos = if Some(c_name) == cache.quot_lift {
            5usize
        } else if Some(c_name) == cache.quot_ind {
            4usize
        } else {
            return None;
        };
        let qmk = self.force_all(*args.get(qmk_pos)?);
        self.fire_quot(c_name, args, qmk)
    }

    fn fire_quot(&mut self, c_name: NamePtr<'t>, args: &[V<'t>], qmk: V<'t>) -> Option<V<'t>> {
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
        let qmk_args = self.spine_apps(qmk_spine)?;
        if qmk_args.len() != 3 {
            return None;
        }
        let f = *args.get(3)?;
        let last = qmk_args[2];
        let mut result = self.apply_v(f, last);
        for a in &args[rest_idx..] {
            result = self.apply_v(result, a);
        }
        Some(result)
    }

    fn do_nat_red(&mut self, name: NamePtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        self.do_nat_red_at(name, args, true)
    }

    fn do_nat_red_shallow(&mut self, name: NamePtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        self.do_nat_red_at(name, args, false)
    }

    fn do_nat_red_at(&mut self, name: NamePtr<'t>, args: &[V<'t>], deep: bool) -> Option<V<'t>> {
        let cache = self.ctx.export_file.name_cache;
        if args.len() == 1 && Some(name) == cache.nat_succ {
            let n = self.value_to_bignum_at(args[0], deep)?;
            return self.mk_natlit_val(n + 1u8);
        }
        if args.len() == 5 && (Some(name) == cache.nat_div_go || Some(name) == cache.nat_mod_core_go) {
            let y = self.value_to_bignum_at(args[0], deep)?;
            let x = self.value_to_bignum_at(args[3], deep)?;
            let op = if Some(name) == cache.nat_div_go { NatBinOp::Div } else { NatBinOp::Mod };
            return self.do_nat_bin_val(x, y, op);
        }
        if args.len() != 2 {
            return None;
        }
        let op = if Some(name) == cache.nat_add {
            NatBinOp::Add
        } else if Some(name) == cache.nat_sub {
            NatBinOp::Sub
        } else if Some(name) == cache.nat_mul {
            NatBinOp::Mul
        } else if Some(name) == cache.nat_pow {
            NatBinOp::Pow
        } else if Some(name) == cache.nat_mod {
            NatBinOp::Mod
        } else if Some(name) == cache.nat_div {
            NatBinOp::Div
        } else if Some(name) == cache.nat_beq {
            NatBinOp::Beq
        } else if Some(name) == cache.nat_ble {
            NatBinOp::Ble
        } else if Some(name) == cache.nat_land {
            NatBinOp::LAnd
        } else if Some(name) == cache.nat_lor {
            NatBinOp::LOr
        } else if Some(name) == cache.nat_xor {
            NatBinOp::XOr
        } else if Some(name) == cache.nat_gcd {
            NatBinOp::Gcd
        } else if Some(name) == cache.nat_shl {
            NatBinOp::Shl
        } else if Some(name) == cache.nat_shr {
            NatBinOp::Shr
        } else {
            return None;
        };
        let xn = self.value_to_bignum_at(args[0], deep)?;
        let yn = self.value_to_bignum_at(args[1], deep)?;
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

    pub(crate) fn value_has_free_bvar(&mut self, v: V<'t>) -> bool {
        let v = self.force_thunk(v);
        let key = v as *const Value<'t> as usize;
        if let Some(&b) = self.tc_cache.fvar_cache.get(&key) {
            return b;
        }
        let r = match v {
            Value::Sort { .. } | Value::NatLit { .. } | Value::StrLit { .. } => false,
            Value::Rigid { head: RigidHead::BVar(..) | RigidHead::Local(..), .. } => true,
            Value::Rigid { spine, .. } | Value::Unfold { spine, .. } => {
                let mut found = false;
                let mut s = *spine;
                loop {
                    match s {
                        Spine::Empty => break,
                        Spine::Snoc(prev, elim) => {
                            if let Elim::App(a) = elim {
                                if self.value_has_free_bvar(a) {
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

    pub(crate) fn value_to_bignum(&mut self, v: V<'t>) -> Option<BigUint> { self.value_to_bignum_at(v, true) }

    fn value_to_bignum_at(&mut self, v: V<'t>, deep: bool) -> Option<BigUint> {
        let mut succs: u64 = 0;
        let mut cur = self.force_thunk(v);
        loop {
            match cur {
                Value::NatLit { ptr } => {
                    return self.ctx.read_bignum(*ptr).cloned().map(|n| n + succs);
                }
                Value::Rigid { head: RigidHead::Ctor(name, _), spine, .. } => {
                    if Some(*name) == self.ctx.export_file.name_cache.nat_zero && spine.is_empty() {
                        return Some(BigUint::from(succs));
                    }
                    if Some(*name) == self.ctx.export_file.name_cache.nat_succ {
                        if let Spine::Snoc(Spine::Empty, Elim::App(a)) = spine {
                            succs += 1;
                            cur = self.force_thunk(a);
                            continue;
                        }
                    }
                    return None;
                }
                Value::Unfold { head_value, .. } => {
                    if let Some(Value::NatLit { ptr }) = head_value.get() {
                        return self.ctx.read_bignum(*ptr).cloned().map(|n| n + succs);
                    }
                    if !deep {
                        return None;
                    }
                    return self.bignum_via_force(cur).map(|n| n + succs);
                }
                Value::Rigid { head: RigidHead::Recursor(..) | RigidHead::QuotConst(..), .. } => {
                    if !deep {
                        return None;
                    }
                    return self.bignum_via_force(cur).map(|n| n + succs);
                }
                _ => return None,
            }
        }
    }

    fn bignum_via_force(&mut self, v: V<'t>) -> Option<BigUint> {
        if self.value_has_free_bvar(v) {
            return None;
        }
        let f = self.force_all(v);
        match f {
            Value::NatLit { ptr } => self.ctx.read_bignum(*ptr).cloned(),
            Value::Rigid { head: RigidHead::Ctor(name, _), .. }
                if Some(*name) == self.ctx.export_file.name_cache.nat_zero
                    || Some(*name) == self.ctx.export_file.name_cache.nat_succ =>
            {
                if std::ptr::eq(f, v) {
                    return None;
                }
                self.value_to_bignum(f)
            }
            _ => None,
        }
    }
}
