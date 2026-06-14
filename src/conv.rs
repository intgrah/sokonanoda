use crate::env::{ConstructorData, Declar, ReducibilityHint};
use crate::tc::TypeChecker;
use crate::util::{ExprPtr, LevelPtr, NamePtr};
use crate::value::{self, Elim, Env, RigidHead, Spine, UnfoldHead, Value, E, S, V};
fn rigid_head_eq<'a>(hx: RigidHead<'a>, hy: RigidHead<'a>) -> bool {
    match (hx, hy) {
        (RigidHead::BVar(a, _), RigidHead::BVar(b, _)) => a == b,
        (RigidHead::Local(a), RigidHead::Local(b)) => a == b,
        _ => false,
    }
}

#[inline]
fn is_cacheable<'a>(v: &Value<'a>) -> bool {
    matches!(
        v,
        Value::Pi { .. }
            | Value::Lam { .. }
            | Value::Unfold { .. }
            | Value::Rigid { head: RigidHead::Recursor(..) | RigidHead::QuotConst(..), .. }
    )
}

impl<'x, 't, 'p> TypeChecker<'x, 't, 'p> {
    pub(crate) fn def_eq_core(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        let env = self.empty_env();
        let vx = self.eval(env, x);
        let vy = self.eval(env, y);
        if self.try_top_proof_irrel(vx, vy) {
            return true;
        }
        self.conv_types(vx, vy)
    }

    pub(crate) fn conv_types(&mut self, a: V<'t>, b: V<'t>) -> bool { self.unify::<true>(0, a, b) }

    pub(crate) fn conv_types_at(&mut self, depth: u32, a: V<'t>, b: V<'t>) -> bool { self.unify::<true>(depth, a, b) }

    #[inline]
    fn envs_ptr_equal(e1: E<'t>, e2: E<'t>) -> bool {
        let mut a = e1;
        let mut b = e2;
        loop {
            if std::ptr::eq(a, b) {
                return true;
            }
            match (a, b) {
                (Env::Nil, Env::Nil) => return true,
                (Env::Cons { v: va, parent: pa, hash: ha }, Env::Cons { v: vb, parent: pb, hash: hb }) => {
                    if ha != hb {
                        return false;
                    }
                    if !std::ptr::eq(*va, *vb) {
                        return false;
                    }
                    a = *pa;
                    b = *pb;
                }
                _ => return false,
            }
        }
    }

    #[inline]
    fn unify<const RIGID: bool>(&mut self, depth: u32, mut x: V<'t>, mut y: V<'t>) -> bool {
        loop {
            x = self.force_thunk(x);
            y = self.force_thunk(y);
            if std::ptr::eq(x, y) {
                return true;
            }
            match (x, y) {
                (
                    Value::Rigid { head: RigidHead::BVar(la, _), spine: sx },
                    Value::Rigid { head: RigidHead::BVar(lb, _), spine: sy },
                ) if la == lb => match (*sx, *sy) {
                    (
                        Spine::Snoc { prev: Spine::Empty, elim: Elim::App(va) },
                        Spine::Snoc { prev: Spine::Empty, elim: Elim::App(vb) },
                    ) => {
                        x = va;
                        y = vb;
                    }
                    _ => return self.unify_general::<RIGID>(depth, x, y),
                },
                _ => return self.unify_general::<RIGID>(depth, x, y),
            }
        }
    }

    #[inline]
    fn unify_general<const RIGID: bool>(&mut self, depth: u32, x: V<'t>, y: V<'t>) -> bool {
        let cacheable = is_cacheable(x) || is_cacheable(y);
        let neg_eligible = !matches!(x, Value::Lam { .. }) && !matches!(y, Value::Lam { .. });
        if cacheable {
            let xa = x as *const Value<'t> as usize;
            let ya = y as *const Value<'t> as usize;
            let cache_key = if xa < ya { (xa, ya) } else { (ya, xa) };
            if self.tc_cache.conv_cache.contains(&cache_key) {
                return true;
            }
            if RIGID && neg_eligible {
                if self.tc_cache.conv_cache_neg.contains(&cache_key) {
                    return false;
                }
                if self.tc_cache.probe_depth > 0 && self.tc_cache.conv_cache_neg_probe.contains(&cache_key) {
                    return false;
                }
            }
            let result = self.unify_no_cache::<RIGID>(depth, x, y);
            if result {
                self.tc_cache.conv_cache.insert(cache_key);
            } else if RIGID && neg_eligible {
                if self.tc_cache.probe_depth == 0 {
                    self.tc_cache.conv_cache_neg.insert(cache_key);
                } else {
                    self.tc_cache.conv_cache_neg_probe.insert(cache_key);
                }
            }
            result
        } else {
            self.unify_no_cache::<RIGID>(depth, x, y)
        }
    }

    fn unify_no_cache<const RIGID: bool>(&mut self, depth: u32, x: V<'t>, y: V<'t>) -> bool {
        let (t, t2) = (self.force_thunk(x), self.force_thunk(y));
        if let Some(r) = self.conv_nat::<RIGID>(depth, t, t2) {
            return r;
        }
        if self.unify_direct::<RIGID>(depth, t, t2) {
            return true;
        }
        self.unify_cold::<RIGID>(depth, t, t2)
    }

    fn unify_direct<const RIGID: bool>(&mut self, depth: u32, t: V<'t>, t2: V<'t>) -> bool {
        match (t, t2) {
            (Value::Sort { level: lx }, Value::Sort { level: ly }) => self.ctx.eq_antisymm(*lx, *ly),
            (Value::NatLit { ptr: px }, Value::NatLit { ptr: py }) => px == py,
            (Value::StrLit { ptr: px }, Value::StrLit { ptr: py }) => px == py,

            (Value::Rigid { head: hx, spine: sx }, Value::Rigid { head: hy, spine: sy }) if rigid_head_eq(*hx, *hy) =>
                self.unify_spine::<RIGID>(depth, sx, sy),

            (
                Value::Rigid { head: RigidHead::Ctor(nx, lx), spine: sx },
                Value::Rigid { head: RigidHead::Ctor(ny, ly), spine: sy },
            ) if nx == ny && self.ctx.eq_antisymm_many(*lx, *ly) => self.unify_spine::<RIGID>(depth, sx, sy),
            (
                Value::Rigid { head: RigidHead::Inductive(nx, lx), spine: sx },
                Value::Rigid { head: RigidHead::Inductive(ny, ly), spine: sy },
            ) if nx == ny && self.ctx.eq_antisymm_many(*lx, *ly) => self.unify_spine::<RIGID>(depth, sx, sy),
            (
                Value::Rigid { head: RigidHead::Axiom(nx, lx), spine: sx },
                Value::Rigid { head: RigidHead::Axiom(ny, ly), spine: sy },
            ) if nx == ny && self.ctx.eq_antisymm_many(*lx, *ly) => self.unify_spine::<RIGID>(depth, sx, sy),

            (
                Value::Rigid { head: RigidHead::Recursor(nx, lx), spine: sx },
                Value::Rigid { head: RigidHead::Recursor(ny, ly), spine: sy },
            ) => {
                let (nx, ny, lx, ly) = (*nx, *ny, *lx, *ly);
                let heads_match = nx == ny && self.ctx.eq_antisymm_many(lx, ly);
                self.unify_iota::<RIGID>(depth, t, t2, heads_match, sx, sy)
            }
            (
                Value::Rigid { head: RigidHead::QuotConst(nx, lx), spine: sx },
                Value::Rigid { head: RigidHead::QuotConst(ny, ly), spine: sy },
            ) => {
                let (nx, ny, lx, ly) = (*nx, *ny, *lx, *ly);
                let heads_match = nx == ny && self.ctx.eq_antisymm_many(lx, ly);
                self.unify_iota::<RIGID>(depth, t, t2, heads_match, sx, sy)
            }

            (Value::Pi { domain: dx, body: bx, .. }, Value::Pi { domain: dy, body: by, .. }) => {
                if bx.body == by.body && std::ptr::eq(*dx, *dy) && Self::envs_ptr_equal(bx.env, by.env) {
                    return true;
                }
                if !self.unify::<RIGID>(depth, dx, dy) {
                    return false;
                }
                let dx = *dx;
                let fresh = self.mk_bvar_hc(depth, dx);
                let vx = self.apply_closure_v(bx, fresh);
                let vy = self.apply_closure_v(by, fresh);
                self.unify::<RIGID>(depth + 1, vx, vy)
            }

            (Value::Lam { body: bx, .. }, Value::Lam { body: by, .. }) => {
                if bx.body == by.body && Self::envs_ptr_equal(bx.env, by.env) {
                    return true;
                }
                let dx = self.lam_domain(t);
                let fresh = self.mk_bvar_hc(depth, dx);
                let vx = self.apply_closure_v(bx, fresh);
                let vy = self.apply_closure_v(by, fresh);
                self.unify::<RIGID>(depth + 1, vx, vy)
            }

            (
                Value::Unfold { head: UnfoldHead { name: nx, levels: lx }, spine: sx, .. },
                Value::Unfold { head: UnfoldHead { name: ny, levels: ly }, spine: sy, .. },
            ) => {
                let heads_match = nx == ny && self.ctx.eq_antisymm_many(*lx, *ly);
                let (nx, ny) = (*nx, *ny);
                let sx = *sx;
                let sy = *sy;
                if RIGID {
                    if heads_match && self.spine_probe(depth, sx, sy) {
                        return true;
                    }
                    if self.try_proof_irrel_at(depth, t, t2) {
                        return true;
                    }
                    if heads_match {
                        return self.unfold_pair(depth, t, t2);
                    }
                    let lh = self.unfold_hint(nx);
                    let rh = self.unfold_hint(ny);
                    if lh.is_lt(&rh) {
                        let v2 = self.unfold_value(t2);
                        if !std::ptr::eq(v2, t2) {
                            return self.unify::<true>(depth, t, v2);
                        }
                        let v1 = self.unfold_value(t);
                        if !std::ptr::eq(v1, t) {
                            return self.unify::<true>(depth, v1, t2);
                        }
                        let f2 = self.unfold_value_demand(t2);
                        if std::ptr::eq(f2, t2) {
                            return false;
                        }
                        self.unify::<true>(depth, t, f2)
                    } else if rh.is_lt(&lh) {
                        let v1 = self.unfold_value(t);
                        if !std::ptr::eq(v1, t) {
                            return self.unify::<true>(depth, v1, t2);
                        }
                        let v2 = self.unfold_value(t2);
                        if !std::ptr::eq(v2, t2) {
                            return self.unify::<true>(depth, t, v2);
                        }
                        let f1 = self.unfold_value_demand(t);
                        if std::ptr::eq(f1, t) {
                            return false;
                        }
                        self.unify::<true>(depth, f1, t2)
                    } else {
                        self.unfold_pair(depth, t, t2)
                    }
                } else if heads_match {
                    self.unify_spine::<false>(depth, sx, sy)
                } else {
                    false
                }
            }

            (Value::Unfold { .. }, _) if RIGID => {
                if self.try_proof_irrel_at(depth, t, t2) {
                    return true;
                }
                let v1 = self.unfold_value(t);
                if std::ptr::eq(v1, t) {
                    let f1 = self.unfold_value_demand(t);
                    if std::ptr::eq(f1, t) {
                        return false;
                    }
                    return self.unify::<true>(depth, f1, t2);
                }
                self.unify::<true>(depth, v1, t2)
            }
            (_, Value::Unfold { .. }) if RIGID => {
                if self.try_proof_irrel_at(depth, t, t2) {
                    return true;
                }
                let v2 = self.unfold_value(t2);
                if std::ptr::eq(v2, t2) {
                    let f2 = self.unfold_value_demand(t2);
                    if std::ptr::eq(f2, t2) {
                        return false;
                    }
                    return self.unify::<true>(depth, t, f2);
                }
                self.unify::<true>(depth, t, v2)
            }

            (Value::Rigid { head: RigidHead::Recursor(..) | RigidHead::QuotConst(..), .. }, _) if RIGID => {
                if self.try_proof_irrel_at(depth, t, t2) {
                    return true;
                }
                if let Some(v1) = self.iota_value(t) {
                    return self.unify::<true>(depth, v1, t2);
                }
                if matches!(t2, Value::Rigid { head: RigidHead::Recursor(..) | RigidHead::QuotConst(..), .. }) {
                    if let Some(v2) = self.iota_value(t2) {
                        return self.unify::<true>(depth, t, v2);
                    }
                }
                if matches!(t2, Value::Unfold { .. }) {
                    let v2 = self.unfold_value_demand(t2);
                    if !std::ptr::eq(v2, t2) {
                        return self.unify::<true>(depth, t, v2);
                    }
                }
                false
            }
            (_, Value::Rigid { head: RigidHead::Recursor(..) | RigidHead::QuotConst(..), .. }) if RIGID => {
                if self.try_proof_irrel_at(depth, t, t2) {
                    return true;
                }
                if let Some(v2) = self.iota_value(t2) {
                    return self.unify::<true>(depth, t, v2);
                }
                if matches!(t, Value::Unfold { .. }) {
                    let v1 = self.unfold_value_demand(t);
                    if !std::ptr::eq(v1, t) {
                        return self.unify::<true>(depth, v1, t2);
                    }
                }
                false
            }

            _ => false,
        }
    }

    fn spine_probe(&mut self, depth: u32, sx: S<'t>, sy: S<'t>) -> bool {
        self.tc_cache.probe_depth += 1;
        let ok = self.unify_spine::<true>(depth, sx, sy);
        self.tc_cache.probe_depth -= 1;
        ok
    }

    fn unfold_pair(&mut self, depth: u32, t: V<'t>, t2: V<'t>) -> bool {
        let v1 = self.unfold_value(t);
        let v2 = self.unfold_value(t2);
        if std::ptr::eq(v1, t) && std::ptr::eq(v2, t2) {
            let f1 = self.unfold_value_demand(t);
            let f2 = self.unfold_value_demand(t2);
            if std::ptr::eq(f1, t) && std::ptr::eq(f2, t2) {
                return false;
            }
            return self.unify::<true>(depth, f1, f2);
        }
        self.unify::<true>(depth, v1, v2)
    }

    fn unify_iota<const RIGID: bool>(
        &mut self,
        depth: u32,
        t: V<'t>,
        t2: V<'t>,
        heads_match: bool,
        sx: S<'t>,
        sy: S<'t>,
    ) -> bool {
        if RIGID {
            if heads_match && self.spine_probe(depth, sx, sy) {
                return true;
            }
            if self.try_proof_irrel_at(depth, t, t2) {
                return true;
            }
            let v1 = self.iota_or_self(t);
            let v2 = self.iota_or_self(t2);
            let progressed = !std::ptr::eq(v1, t) || !std::ptr::eq(v2, t2);
            if progressed {
                return self.unify::<true>(depth, v1, v2);
            }
            if heads_match {
                return self.unify_spine::<true>(depth, sx, sy);
            }
            false
        } else if heads_match {
            self.unify_spine::<false>(depth, sx, sy)
        } else {
            false
        }
    }

    fn iota_or_self(&mut self, v: V<'t>) -> V<'t> { self.iota_value(v).unwrap_or(v) }

    fn unfold_hint(&self, name: NamePtr<'t>) -> ReducibilityHint {
        match self.env.get_declar(&name) {
            Some(Declar::Definition { hint, .. }) => *hint,
            _ => ReducibilityHint::Opaque,
        }
    }

    fn unify_spine<const RIGID: bool>(&mut self, depth: u32, sx: S<'t>, sy: S<'t>) -> bool {
        match (sx, sy) {
            (Spine::Empty, Spine::Empty) => true,
            (Spine::Snoc { prev: pa, elim: ea }, Spine::Snoc { prev: pb, elim: eb }) => {
                if !self.unify_spine::<RIGID>(depth, pa, pb) {
                    return false;
                }
                match (ea, eb) {
                    (Elim::App(va), Elim::App(vb)) => self.unify::<RIGID>(depth, va, vb),
                    (Elim::Proj { ty_name: tx, idx: ix }, Elim::Proj { ty_name: ty, idx: iy }) => tx == ty && ix == iy,
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn unify_cold<const RIGID: bool>(&mut self, depth: u32, x: V<'t>, y: V<'t>) -> bool {
        if !RIGID {
            return false;
        }
        if self.try_proof_irrel_at(depth, x, y) {
            return true;
        }
        match (x, y) {
            (Value::Lam { body, .. }, _) if !matches!(y, Value::Lam { .. }) => {
                let domain = self.lam_domain(x);
                let fresh = self.mk_bvar_hc(depth, domain);
                let lhs = self.apply_closure_v(body, fresh);
                let rhs = self.apply_v(y, fresh);
                return self.unify::<true>(depth + 1, lhs, rhs);
            }
            (_, Value::Lam { body, .. }) if !matches!(x, Value::Lam { .. }) => {
                let domain = self.lam_domain(y);
                let fresh = self.mk_bvar_hc(depth, domain);
                let lhs = self.apply_v(x, fresh);
                let rhs = self.apply_closure_v(body, fresh);
                return self.unify::<true>(depth + 1, lhs, rhs);
            }
            _ => {}
        }
        self.try_struct_eta(depth, x, y)
    }

    fn try_struct_eta(&mut self, depth: u32, x: V<'t>, y: V<'t>) -> bool {
        let xt = self.value_type_opt(x);
        let yt = self.value_type_opt(y);
        for ty in [xt, yt].into_iter().flatten() {
            let ty_f = self.force_all(ty);
            if let Value::Rigid { head: RigidHead::Inductive(ind_name, _), .. } = ty_f {
                let ind_name = *ind_name;
                if self.is_unit_inductive(ind_name) {
                    return true;
                }
                if self.env.can_be_struct(&ind_name)
                    && (self.try_eta_struct_v(depth, ind_name, x, y) || self.try_eta_struct_v(depth, ind_name, y, x))
                {
                    return true;
                }
            }
        }
        false
    }

    fn value_type_opt(&mut self, v: V<'t>) -> Option<V<'t>> {
        match v {
            Value::Pi { .. } | Value::Lam { .. } => None,
            _ => Some(self.value_type(v)),
        }
    }

    pub(crate) fn try_top_proof_irrel(&mut self, x: V<'t>, y: V<'t>) -> bool { self.try_proof_irrel_at(0, x, y) }

    fn try_proof_irrel_at(&mut self, depth: u32, x: V<'t>, y: V<'t>) -> bool {
        if matches!(x, Value::Lam { .. }) || matches!(y, Value::Lam { .. }) {
            return self.try_proof_irrel_lam(depth, x, y);
        }
        if !matches!(x, Value::Rigid { .. } | Value::Unfold { .. }) {
            return false;
        }
        if !matches!(y, Value::Rigid { .. } | Value::Unfold { .. }) {
            return false;
        }
        let tx = self.value_type(x);
        if !self.is_prop_type(tx) {
            return false;
        }
        let ty = self.value_type(y);
        if !self.is_prop_type(ty) {
            return false;
        }
        self.conv_types_at(depth, tx, ty)
    }

    fn is_prop_type(&mut self, t: V<'t>) -> bool {
        if let Some(l) = self.level_of_type(t) {
            self.ctx.is_zero(l)
        } else {
            false
        }
    }

    fn try_proof_irrel_lam(&mut self, depth: u32, x: V<'t>, y: V<'t>) -> bool {
        let lam_side = match (x, y) {
            (Value::Lam { .. }, _) => x,
            (_, Value::Lam { .. }) => y,
            _ => return false,
        };
        let domain = self.lam_domain(lam_side);
        let fresh = self.mk_bvar_hc(depth, domain);
        let xb = self.apply_v(x, fresh);
        let yb = self.apply_v(y, fresh);
        self.try_proof_irrel_at(depth + 1, xb, yb)
    }

    fn try_eta_struct_v(&mut self, depth: u32, ind_name: NamePtr<'t>, x: V<'t>, y: V<'t>) -> bool {
        let (yname, yspine) = match y {
            Value::Rigid { head: RigidHead::Ctor(name, _), spine } => (*name, *spine),
            _ => return false,
        };
        let (inductive_name, num_params, num_fields) = match self.env.get_constructor(&yname) {
            Some(ConstructorData { inductive_name, num_params, num_fields, .. }) =>
                (*inductive_name, *num_params, *num_fields),
            None => return false,
        };
        if inductive_name != ind_name {
            return false;
        }
        if yspine.len() != u32::from(num_params + num_fields) {
            return false;
        }
        let yargs: Vec<V<'t>> = match self.spine_apps(yspine) {
            Some(v) => v,
            None => return false,
        };
        for i in 0..usize::from(num_fields) {
            let proj = self.do_proj(ind_name, i, x);
            let rhs = yargs[usize::from(num_params) + i];
            if !self.unify::<true>(depth, proj, rhs) {
                return false;
            }
        }
        true
    }

    fn is_unit_inductive(&self, ind_name: NamePtr<'t>) -> bool {
        let ind = match self.env.get_inductive(&ind_name) {
            Some(i) => i,
            None => return false,
        };
        if ind.all_ctor_names.len() != 1 || ind.num_indices != 0 {
            return false;
        }
        let ctor = match self.env.get_constructor(&ind.all_ctor_names[0]) {
            Some(c) => c,
            None => return false,
        };
        ctor.num_fields == 0
    }

    fn conv_nat<const RIGID: bool>(&mut self, depth: u32, x: V<'t>, y: V<'t>) -> Option<bool> {
        if !self.may_be_nat(x) && !self.may_be_nat(y) {
            return None;
        }
        if matches!(x, Value::NatLit { .. }) && matches!(y, Value::NatLit { .. }) {
            return None;
        }
        let xz = self.value_is_nat_zero(x);
        let yz = self.value_is_nat_zero(y);
        if xz && yz {
            return Some(true);
        }
        let px = self.value_nat_pred(x);
        let py = self.value_nat_pred(y);
        match (px, py) {
            (Some(a), Some(b)) => Some(self.unify::<RIGID>(depth, a, b)),
            _ => None,
        }
    }

    fn may_be_nat(&self, v: V<'t>) -> bool {
        match v {
            Value::NatLit { .. } => true,
            Value::Rigid { head: RigidHead::Ctor(name, _), .. } => {
                let nc = &self.ctx.export_file.name_cache;
                Some(*name) == nc.nat_zero || Some(*name) == nc.nat_succ
            }
            _ => false,
        }
    }

    fn value_is_nat_zero(&self, v: V<'t>) -> bool {
        match v {
            Value::Rigid { head: RigidHead::Ctor(name, _), spine } =>
                Some(*name) == self.ctx.export_file.name_cache.nat_zero && spine.is_empty(),
            Value::NatLit { ptr } => {
                use num_traits::Zero;
                self.ctx.read_bignum(*ptr).map(|n| n.is_zero()).unwrap_or(false)
            }
            _ => false,
        }
    }

    fn value_nat_pred(&mut self, v: V<'t>) -> Option<V<'t>> {
        match v {
            Value::Rigid { head: RigidHead::Ctor(name, _), spine } => {
                if Some(*name) == self.ctx.export_file.name_cache.nat_succ {
                    if let Spine::Snoc { prev: Spine::Empty, elim: Elim::App(a) } = **spine {
                        return Some(a);
                    }
                }
                None
            }
            Value::NatLit { ptr } => {
                use num_traits::Zero;
                let n = self.ctx.read_bignum(*ptr)?.clone();
                if n.is_zero() {
                    return None;
                }
                let pred = self.ctx.alloc_bignum(n - 1u8)?;
                Some(value::mk_natlit(self.arena, pred))
            }
            _ => None,
        }
    }

    fn level_of_type(&mut self, ty: V<'t>) -> Option<LevelPtr<'t>> {
        let ty = self.force_thunk(ty);
        match ty {
            Value::Sort { level } => {
                let s = self.ctx.succ(*level);
                Some(self.ctx.simplify(s))
            }
            Value::Pi { domain, body, .. } => {
                let l_dom = self.level_of_type(domain)?;
                let fresh = self.mk_bvar_hc(0, domain);
                let cod = self.apply_closure_v(body, fresh);
                let cod_f = self.force_all(cod);
                let l_cod = self.level_of_type(cod_f)?;
                let l = self.ctx.imax(l_dom, l_cod);
                Some(self.ctx.simplify(l))
            }
            Value::Rigid {
                head:
                    RigidHead::Axiom(n, ls)
                    | RigidHead::Ctor(n, ls)
                    | RigidHead::Recursor(n, ls)
                    | RigidHead::QuotConst(n, ls)
                    | RigidHead::Inductive(n, ls),
                ..
            } => {
                let (n, ls) = (*n, *ls);
                if let Some(l) = self.const_result_level(n, ls) {
                    return Some(l);
                }
                let t = self.value_type(ty);
                let t_f = self.force_all(t);
                match t_f {
                    Value::Sort { level } => Some(self.ctx.simplify(*level)),
                    _ => None,
                }
            }
            Value::Unfold { head: UnfoldHead { name, levels }, .. } => {
                let t = self.value_type(ty);
                let t_f = self.force_all(t);
                if let Value::Sort { level } = t_f {
                    return Some(self.ctx.simplify(*level));
                }
                self.const_result_level(*name, *levels)
            }
            Value::Rigid { head: RigidHead::BVar(..) | RigidHead::Local(..), .. } => {
                let t = self.value_type(ty);
                let ty_f = self.force_all(t);
                match ty_f {
                    Value::Sort { level } => Some(self.ctx.simplify(*level)),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}
