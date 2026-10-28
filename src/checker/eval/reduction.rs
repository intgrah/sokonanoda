// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::memo;
use crate::checker::env::{Declar, RecursorData};
use crate::checker::nat::{
    nat_div, nat_gcd, nat_land, nat_lor, nat_mod, nat_shl, nat_shr, nat_sub, nat_xor,
};
use crate::checker::tc::TypeChecker;
use crate::checker::value::{EMPTY_ENV, Elim, ElimView, RigidHead, Spine, V, VT, Value};
use crate::outcome::reject;
use crate::term::id::{BigId, LevelsId, NameId, StrId};
use num_bigint::BigUint;
use num_traits::pow::Pow;

enum ForceStep {
    Reduced(V),
    Descend(V),
    Done,
}

impl<'t> TypeChecker<'_, 't> {
    pub(crate) fn ctor_shape(&mut self, name: NameId) -> Option<(u16, u16, NameId)> {
        self.env
            .get_constructor(name)
            .map(|c| (c.num_params, c.num_fields, c.inductive_name))
    }

    pub(crate) fn can_be_struct_memo(&mut self, name: NameId) -> bool {
        self.env.can_be_struct(name)
    }

    pub(crate) fn do_proj(&mut self, depth: u32, ty_name: NameId, idx: u16, v: V) -> V {
        let v = self.whnf_head(depth, v);
        match self.val(v) {
            Value::Rigid {
                head: RigidHead::Ctor(ctor_name, _),
                spine,
                ..
            } => {
                if let Some((num_params, _, inductive_name)) = self.ctor_shape(ctor_name)
                    && inductive_name == ty_name
                {
                    let np = usize::from(num_params);
                    if let Some(ElimView::App(field)) = self
                        .vals()
                        .spine_get(spine, np + usize::from(idx))
                        .map(Elim::view)
                    {
                        return field;
                    }
                }
                self.proj_extend_spine(ty_name, idx, v)
            }
            Value::NatLit { lit, .. } => {
                let ctor = self
                    .nat_lit_to_ctor_val(depth, lit)
                    .expect("do_proj: nat_lit_to_ctor_val failed");
                self.do_proj(depth, ty_name, idx, ctor)
            }
            Value::StrLit { lit, .. } => {
                let ctor = self
                    .str_lit_to_ctor_val(depth, lit)
                    .expect("do_proj: str_lit_to_ctor_val failed");
                self.do_proj(depth, ty_name, idx, ctor)
            }
            Value::Rigid { .. } | Value::Unfold { .. } => self.proj_extend_spine(ty_name, idx, v),
            _ => reject!("do_proj: not a neutral"),
        }
    }

    fn proj_extend_spine(&mut self, ty_name: NameId, idx: u16, v: V) -> V {
        match self.val(v) {
            Value::Rigid { spine, .. } | Value::Unfold { spine, .. } => {
                self.spine_snoc_hc(spine, Elim::proj(ty_name, idx))
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn proj_field_type_with(
        &mut self,
        depth: u32,
        struct_value: V,
        struct_ty: V,
        ty_name: NameId,
        idx: u16,
    ) -> Option<V> {
        let struct_ty = self.force_all(depth, struct_ty);
        let (ind_name, ind_levels, args) = match self.val(struct_ty) {
            Value::Rigid {
                head: RigidHead::Inductive(n, ls),
                spine,
                ..
            } => {
                let aa = self.vals().spine_apps(spine)?;
                (n, ls, aa)
            }
            _ => return None,
        };
        if ind_name != ty_name {
            return None;
        }
        let ind = self.env.get_structure(ind_name, true)?;
        let ctor_name = ind.all_ctor_names[0];
        let ctor_info = match self.env.get_declar(ctor_name)? {
            Declar::Constructor(c) => c.info,
            _ => return None,
        };
        let mut cur = self.eval_inst(ctor_info.ty, ctor_info.uparams, ind_levels);
        let num_params = usize::from(ind.num_params);
        for i in 0..num_params {
            let cf = self.force_all(depth, cur);
            match self.val(cf) {
                Value::Pi { domain, body, .. } => {
                    let arg = *args.get(i)?;
                    cur = self.apply_closure(depth, body, arg, Some(domain));
                }
                _ => return None,
            }
        }
        for i in 0..idx {
            let cf = self.force_all(depth, cur);
            match self.val(cf) {
                Value::Pi { domain, body, .. } => {
                    let prior = self.do_proj(depth, ty_name, i, struct_value);
                    cur = self.apply_closure(depth, body, prior, Some(domain));
                }
                _ => return None,
            }
        }
        let cf = self.force_all(depth, cur);
        match self.val(cf) {
            Value::Pi { domain, .. } => Some(domain),
            _ => None,
        }
    }

    #[inline(always)]
    pub(crate) fn force_all(&mut self, depth: u32, v: V) -> V {
        if !matches!(
            self.vals().kind(v),
            VT::Unfold | VT::Recursor | VT::QuotConst
        ) {
            return v;
        }
        if let Some(w) = self.vals().whnf(v) {
            return w;
        }
        let w = self.force_reducible(depth, v);
        self.vals_mut().set_whnf(v, w);
        w
    }

    #[inline(always)]
    pub(crate) fn force_all_val(&mut self, depth: u32, v: V) -> Value {
        let f = self.force_all(depth, v);
        self.val(f)
    }

    #[inline(never)]
    fn force_reducible(&mut self, depth: u32, v: V) -> V {
        if let Some(r) = self.store_lookup(depth, v) {
            return r;
        }
        let mut cur = v;
        let mut steps = 0u32;
        let mut waiting: Vec<V> = Vec::new();
        let result = 'done: loop {
            while let Value::Unfold { .. } = self.val(cur) {
                let next = self.unfold_value(depth, cur);
                if next == cur {
                    break;
                }
                steps += 1;
                cur = next;
            }
            let step = match self.val(cur) {
                Value::Rigid {
                    head: RigidHead::Recursor(..) | RigidHead::QuotConst(..),
                    ..
                } => self.iota_step(depth, cur),
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
                        if let Some(res) = self.fire_value(depth, rec_val, cur) {
                            self.vals_mut().set_step(rec_val, res);
                            steps += 1;
                            cur = res;
                            break;
                        }
                        self.vals_mut().set_step(rec_val, rec_val);
                        cur = rec_val;
                    }
                }
            }
        };
        self.note_whnf(depth, v, result, steps);
        result
    }

    fn iota_step(&mut self, depth: u32, v: V) -> ForceStep {
        let key = v;
        match self.vals().step(key) {
            Some(c) if c == key => return ForceStep::Done,
            Some(c) => return ForceStep::Reduced(c),
            None => {}
        }
        match self.val(v) {
            Value::Rigid {
                head: RigidHead::Recursor(name, levels),
                spine,
                ..
            } => {
                let env = self.env;
                let Some(rec) = env.get_recursor(name) else {
                    return ForceStep::Done;
                };
                let Some(args) = self.vals().spine_apps(spine) else {
                    return ForceStep::Done;
                };
                if args.len() <= rec.major_idx() {
                    return ForceStep::Done;
                }
                if let Some(r) = self.k_pre_reduce(depth, rec, levels, &args) {
                    self.vals_mut().set_step(key, r);
                    return ForceStep::Reduced(r);
                }
                let major_h = self.strip_head(depth, args[rec.major_idx()]);
                if self.is_iota_reducible(major_h) {
                    return ForceStep::Descend(major_h);
                }
                if let Some(res) = self.fire_recursor(depth, rec, levels, &args, major_h) {
                    self.vals_mut().set_step(key, res);
                    ForceStep::Reduced(res)
                } else {
                    self.vals_mut().set_step(key, key);
                    ForceStep::Done
                }
            }
            Value::Rigid {
                head: RigidHead::QuotConst(name, _),
                spine,
                ..
            } => {
                let cache = self.ctx.export_file.name_cache;
                let qmk_pos = if Some(name) == cache.quot_lift {
                    5
                } else if Some(name) == cache.quot_ind {
                    4
                } else {
                    return ForceStep::Done;
                };
                let name = name;
                let Some(args) = self.vals().spine_apps(spine) else {
                    return ForceStep::Done;
                };
                let Some(&major) = args.get(qmk_pos) else {
                    return ForceStep::Done;
                };
                let major_h = self.strip_head(depth, major);
                if self.is_iota_reducible(major_h) {
                    return ForceStep::Descend(major_h);
                }
                if let Some(res) = self.fire_quot(depth, name, &args, major_h) {
                    self.vals_mut().set_step(key, res);
                    ForceStep::Reduced(res)
                } else {
                    self.vals_mut().set_step(key, key);
                    ForceStep::Done
                }
            }
            _ => ForceStep::Done,
        }
    }

    fn strip_head(&mut self, depth: u32, v: V) -> V {
        let mut cur = v;
        loop {
            match self.val(cur) {
                Value::Unfold { .. } => {
                    let next = self.unfold_value(depth, cur);
                    if next == cur {
                        return cur;
                    }
                    cur = next;
                }
                _ => return cur,
            }
        }
    }

    fn is_iota_reducible(&self, v: V) -> bool {
        match self.val(v) {
            Value::Rigid {
                head: RigidHead::Recursor(..),
                ..
            } => true,
            Value::Rigid {
                head: RigidHead::QuotConst(name, _),
                ..
            } => {
                let cache = self.ctx.export_file.name_cache;
                Some(name) == cache.quot_lift || Some(name) == cache.quot_ind
            }
            _ => false,
        }
    }

    fn fire_value(&mut self, depth: u32, rec_val: V, major: V) -> Option<V> {
        match self.val(rec_val) {
            Value::Rigid {
                head: RigidHead::Recursor(name, levels),
                spine,
                ..
            } => {
                let env = self.env;
                let rec = env.get_recursor(name)?;
                let args = self.vals().spine_apps(spine)?;
                if args.len() <= rec.major_idx() {
                    return None;
                }
                self.fire_recursor(depth, rec, levels, &args, major)
            }
            Value::Rigid {
                head: RigidHead::QuotConst(name, _),
                spine,
                ..
            } => {
                let args = self.vals().spine_apps(spine)?;
                self.fire_quot(depth, name, &args, major)
            }
            _ => None,
        }
    }

    pub(crate) fn unfold_value(&mut self, depth: u32, v: V) -> V {
        self.unfold_value_go(depth, v, false, true)
    }

    pub(crate) fn unfold_value_demand(&mut self, depth: u32, v: V) -> V {
        self.unfold_value_go(depth, v, self.tc_cache.probe_depth == 0, true)
    }

    pub(crate) fn unfold_value_for_conv(&mut self, depth: u32, v: V, other: V, force: bool) -> V {
        let native = !self.value_has_free_bvar(v) && !self.value_has_free_bvar(other);
        if native {
            if force {
                self.unfold_value_demand(depth, v)
            } else {
                self.unfold_value(depth, v)
            }
        } else {
            self.unfold_value_go(depth, v, force && self.tc_cache.probe_depth == 0, false)
        }
    }

    fn unfold_value_go(&mut self, depth: u32, v: V, force: bool, native: bool) -> V {
        if let Value::Unfold {
            head,
            spine,
            head_value,
        } = self.val(v)
        {
            let head_value_node = head_value;
            let arithmetic =
                self.nat_extension && self.ctx.export_file.nat_red(head.name).is_some();
            let symbolic = arithmetic && !native;
            if v != head_value {
                let cached = if symbolic {
                    self.tc_cache.arithmetic_delta_cache.get(&v)
                } else {
                    self.vals().step(v)
                };
                if let Some(f) = cached {
                    return f;
                }
            }
            if arithmetic && let Some(args) = self.vals().spine_apps(spine) {
                if !symbolic && let Some(r) = self.do_nat_red(depth, head.name, &args) {
                    self.vals_mut().set_step(v, r);
                    return r;
                }
                if !force && self.nat_red_defer(head.name, &args) {
                    return v;
                }
            }
            let head_value = if let Some(hv) = self.vals().step(head_value) {
                if hv == head_value {
                    return v;
                }
                hv
            } else {
                let Some(hv) = self.unfold_const(head.name, head.levels) else {
                    self.vals_mut().set_step(head_value, head_value);
                    self.vals_mut().set_step(v, v);
                    return v;
                };
                self.vals_mut().set_step(head_value, hv);
                hv
            };
            if v == head_value_node {
                return head_value;
            }
            let (args, projs) = self.vals().spine_split(spine);
            let mut cur = head_value;
            let mut from = 0;
            for (at, ty_name, idx) in projs {
                if at > from {
                    cur = self.apply_many(depth, cur, &args[from..at]);
                    from = at;
                }
                cur = self.do_proj(depth, ty_name, idx, cur);
            }
            if from < args.len() {
                cur = self.apply_many(depth, cur, &args[from..]);
            }
            if symbolic {
                self.tc_cache.arithmetic_delta_cache.insert(v, cur);
            } else {
                self.vals_mut().set_step(v, cur);
            }
            return cur;
        }
        v
    }

    pub(crate) fn iota_value(&mut self, depth: u32, v: V) -> Option<V> {
        let v_key = v;
        match self.vals().step(v_key) {
            Some(c) if c == v_key => return None,
            Some(c) => return Some(c),
            None => {}
        }
        let result = match self.val(v) {
            Value::Rigid {
                head: RigidHead::Recursor(name, levels),
                spine,
                ..
            } => {
                let args = self.vals().spine_apps(spine)?;
                self.do_recursor_iota(depth, name, levels, &args)
            }
            Value::Rigid {
                head: RigidHead::QuotConst(name, _),
                spine,
                ..
            } => {
                let args = self.vals().spine_apps(spine)?;
                self.do_quot_iota(depth, name, &args)
            }
            _ => None,
        };
        self.vals_mut().set_step(v_key, result.unwrap_or(v_key));
        result
    }

    pub(crate) fn unfold_const(&mut self, name: NameId, levels: LevelsId) -> Option<V> {
        if let Some(cached) = self.tc_cache.unfold_const_cache.get(&(name, levels)) {
            return Some(cached);
        }
        let (def_uparams, def_value) = self.declar_val(name)?;
        if self.ctx.levels(levels).len() != self.ctx.levels(def_uparams).len() {
            return None;
        }
        let v = self.eval_inst(def_value, def_uparams, levels);
        self.tc_cache.unfold_const_cache.insert((name, levels), v);
        Some(v)
    }

    fn do_recursor_iota(
        &mut self,
        depth: u32,
        name: NameId,
        levels: LevelsId,
        args: &[V],
    ) -> Option<V> {
        let env = self.env;
        let rec = env.get_recursor(name)?;
        if args.len() <= rec.major_idx() {
            return None;
        }
        if let Some(r) = self.k_pre_reduce(depth, rec, levels, args) {
            return Some(r);
        }
        let major = self.whnf_head(depth, args[rec.major_idx()]);
        self.fire_recursor(depth, rec, levels, args, major)
    }

    fn k_pre_reduce(
        &mut self,
        depth: u32,
        rec: &RecursorData,
        levels: LevelsId,
        args: &[V],
    ) -> Option<V> {
        if !rec.is_k {
            return None;
        }
        let raw = args[rec.major_idx()];
        let kctor = self.try_k_reduce(depth, raw, rec)?;
        self.fire_recursor(depth, rec, levels, args, kctor)
    }

    pub(super) fn fire_recursor(
        &mut self,
        depth: u32,
        rec: &RecursorData,
        levels: LevelsId,
        args: &[V],
        major: V,
    ) -> Option<V> {
        if self.nat_extension
            && rec.all_inductives.first().copied() == self.ctx.export_file.name_cache.nat
            && let Value::NatLit { lit, .. } = self.val(major)
        {
            return Some(self.nat_rec_natlit(depth, args, lit, rec, levels));
        }
        let major = self
            .major_to_ctor(depth, major)
            .or_else(|| self.try_k_reduce(depth, major, rec))
            .or_else(|| self.try_struct_eta_reduce(depth, major, rec))
            .unwrap_or(major);
        let (ctor_name, ctor_args) = self.vals().as_ctor_app(major)?;
        let rec_rule = rec
            .rec_rules
            .iter()
            .find(|r| r.ctor_name == ctor_name)
            .copied()?;
        let num_extra = ctor_args
            .len()
            .checked_sub(usize::from(rec_rule.ctor_telescope_size_wo_params))?;
        let mut result = memo!(
            self.tc_cache.rec_rule_cache,
            (rec_rule.val, levels),
            self.eval_inst(rec_rule.val, rec.info.uparams, levels)
        );
        let nprefix = usize::from(rec.num_params + rec.num_motives + rec.num_minors);
        result = self.apply_many(depth, result, &args[..nprefix]);
        result = self.apply_many(depth, result, &ctor_args[num_extra..]);
        result = self.apply_many(depth, result, &args[rec.major_idx() + 1..]);
        Some(result)
    }

    fn nat_rec_natlit(
        &mut self,
        depth: u32,
        args: &[V],
        n_lit: BigId,
        rec: &RecursorData,
        levels: LevelsId,
    ) -> V {
        use num_traits::Zero;
        let n = self.ctx.bignum(n_lit).clone();
        let nparams = usize::from(rec.num_params);
        let nmotives = usize::from(rec.num_motives);
        let major_idx = rec.major_idx();
        let zero_case = args[nparams + nmotives];
        let succ_case = args[nparams + nmotives + 1];
        let result = if n.is_zero() {
            zero_case
        } else {
            let pred = n - 1u8;
            let pred_ptr = self
                .ctx
                .alloc_bignum(pred)
                .expect("nat_rec_natlit: alloc pred");
            let pred_val = self.mk_natlit_hc(pred_ptr);
            let mut ih = self.mk_head_hc(RigidHead::Recursor(rec.info.name, levels));
            for &a in &args[..major_idx] {
                ih = self.apply(depth, ih, a);
            }
            ih = self.apply(depth, ih, pred_val);
            let stepped = self.apply(depth, succ_case, pred_val);
            self.apply(depth, stepped, ih)
        };
        self.apply_many(depth, result, &args[major_idx + 1..])
    }

    fn try_struct_eta_reduce(&mut self, depth: u32, major: V, rec: &RecursorData) -> Option<V> {
        if !self.vals().is_neutral(major) {
            return None;
        }
        let rec_induct = rec.get_major_induct(&self.ctx)?;
        if !self.can_be_struct_memo(rec_induct) {
            return None;
        }
        memo!(
            self.tc_cache.struct_eta_cache,
            (major, rec_induct),
            self.try_struct_eta_reduce_uncached(depth, major, rec, rec_induct)
        )
    }

    fn try_struct_eta_reduce_uncached(
        &mut self,
        depth: u32,
        major: V,
        rec: &RecursorData,
        rec_induct: NameId,
    ) -> Option<V> {
        let major_ty = self.value_type(depth, major);
        let major_ty_f = self.force_all(depth, major_ty);
        let (ty_name, ty_levels, ty_args) = self.vals().as_inductive_app(major_ty_f)?;
        if ty_name != rec_induct {
            return None;
        }
        let ind = self.env.get_inductive(ty_name)?;
        let ctor_name = ind.all_ctor_names[0];
        let ctor_data = self.env.get_constructor(ctor_name)?;
        let num_fields = ctor_data.num_fields;
        let np = usize::from(rec.num_params);
        let mut new_ctor = self.mk_head_hc(RigidHead::Ctor(ctor_name, ty_levels));
        for a in ty_args.iter().take(np).copied() {
            new_ctor = self.apply(depth, new_ctor, a);
        }
        for i in 0..num_fields {
            let proj = self.do_proj(depth, ty_name, i, major);
            new_ctor = self.apply(depth, new_ctor, proj);
        }
        Some(new_ctor)
    }

    fn try_k_reduce(&mut self, depth: u32, major: V, rec: &RecursorData) -> Option<V> {
        if !rec.is_k {
            return None;
        }
        if !self.vals().is_neutral(major) {
            return None;
        }
        let major_ty = self.value_type(depth, major);
        let major_ty_f = self.force_all(depth, major_ty);
        let (ty_name, ty_levels, ty_args) = self.vals().as_inductive_app(major_ty_f)?;
        let rec_induct = rec.get_major_induct(&self.ctx)?;
        if ty_name != rec_induct {
            return None;
        }
        let ind = self.env.get_inductive(ty_name)?;
        let ctor_name = ind.all_ctor_names[0];
        let np = usize::from(rec.num_params);
        let ctor_self = rec
            .rec_rules
            .iter()
            .find(|r| r.ctor_name == ctor_name)
            .map_or(0, |r| usize::from(r.ctor_telescope_size_wo_params));
        let take = (np + ctor_self).min(ty_args.len());
        let mut new_ctor = self.mk_head_hc(RigidHead::Ctor(ctor_name, ty_levels));
        for a in ty_args.iter().take(take).copied() {
            new_ctor = self.apply(depth, new_ctor, a);
        }
        let new_ty = self.value_type(depth, new_ctor);
        if !self.conv_types_at(depth, major_ty_f, new_ty) {
            return None;
        }
        Some(new_ctor)
    }

    fn major_to_ctor(&mut self, depth: u32, major: V) -> Option<V> {
        match self.val(major) {
            Value::NatLit { lit, .. } => self.nat_lit_to_ctor_val(depth, lit),
            Value::StrLit { lit, .. } => self.str_lit_to_ctor_val(depth, lit),
            _ => None,
        }
    }

    pub(crate) fn str_lit_to_ctor_val(&mut self, depth: u32, s: StrId) -> Option<V> {
        let ctor_expr = self.ctx.str_lit_to_constructor(s)?;
        let empty = EMPTY_ENV;
        let v = self.eval(depth, empty, ctor_expr);
        Some(self.whnf_head(depth, v))
    }

    fn nat_lit_to_ctor_val(&mut self, depth: u32, n: BigId) -> Option<V> {
        use num_traits::Zero;
        if !self.nat_extension {
            return None;
        }
        let nv = self.ctx.bignum(n).clone();
        let levels = self.ctx.alloc_levels(&[]);
        if nv.is_zero() {
            let zero_name = self.ctx.export_file.name_cache.nat_zero?;
            Some(self.mk_head_hc(RigidHead::Ctor(zero_name, levels)))
        } else {
            let pred = self.ctx.alloc_bignum(core::ops::Sub::sub(nv, 1u8))?;
            let pred_v = self.mk_natlit_hc(pred);
            let succ_name = self.ctx.export_file.name_cache.nat_succ?;
            let succ_v = self.mk_head_hc(RigidHead::Ctor(succ_name, levels));
            Some(self.apply(depth, succ_v, pred_v))
        }
    }

    fn do_quot_iota(&mut self, depth: u32, c_name: NameId, args: &[V]) -> Option<V> {
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

    pub(super) fn fire_quot(
        &mut self,
        depth: u32,
        c_name: NameId,
        args: &[V],
        qmk: V,
    ) -> Option<V> {
        let cache = self.ctx.export_file.name_cache;
        let rest_idx = if Some(c_name) == cache.quot_lift {
            6usize
        } else if Some(c_name) == cache.quot_ind {
            5usize
        } else {
            return None;
        };
        let (qmk_head, qmk_spine) = match self.val(qmk) {
            Value::Rigid {
                head: RigidHead::QuotConst(name, _),
                spine,
                ..
            } => (name, spine),
            _ => return None,
        };
        if Some(qmk_head) != cache.quot_mk {
            return None;
        }
        let qmk_args = self.vals().spine_apps(qmk_spine)?;
        if qmk_args.len() != 3 {
            return None;
        }
        let f = *args.get(3)?;
        let last = qmk_args[2];
        let result = self.apply(depth, f, last);
        Some(self.apply_many(depth, result, &args[rest_idx..]))
    }

    fn do_nat_red(&mut self, depth: u32, name: NameId, args: &[V]) -> Option<V> {
        self.do_nat_red_at(depth, name, args, true)
    }

    fn do_nat_red_at(&mut self, depth: u32, name: NameId, args: &[V], deep: bool) -> Option<V> {
        use crate::term::name::NatRed;
        let kind = self.ctx.export_file.nat_red(name)?;
        if let NatRed::Succ = kind {
            if args.len() != 1 {
                return None;
            }
            let n = self.value_to_bignum_at(depth, args[0], deep)?;
            return self.mk_natlit_val(n + 1u8);
        }
        let (x, y) = if matches!(kind, NatRed::DivGo | NatRed::ModCoreGo) {
            if args.len() != 5 {
                return None;
            }
            let y = self.value_to_bignum_at(depth, args[0], deep)?;
            let x = self.value_to_bignum_at(depth, args[3], deep)?;
            (x, y)
        } else {
            if args.len() != 2 {
                return None;
            }
            let x = self.value_to_bignum_at(depth, args[0], deep)?;
            let y = self.value_to_bignum_at(depth, args[1], deep)?;
            (x, y)
        };
        match kind {
            NatRed::Add => self.mk_natlit_val(x + y),
            NatRed::Sub => self.mk_natlit_val(nat_sub(x, y)),
            NatRed::Mul => self.mk_natlit_val(x * y),
            NatRed::Pow => self.mk_natlit_val(x.pow(y)),
            NatRed::Div | NatRed::DivGo => self.mk_natlit_val(nat_div(x, y)),
            NatRed::Mod | NatRed::ModCoreGo => self.mk_natlit_val(nat_mod(x, y)),
            NatRed::Gcd => self.mk_natlit_val(nat_gcd(&x, &y)),
            NatRed::LAnd => self.mk_natlit_val(nat_land(x, y)),
            NatRed::LOr => self.mk_natlit_val(nat_lor(x, y)),
            NatRed::XOr => self.mk_natlit_val(nat_xor(&x, &y)),
            NatRed::Shl => self.mk_natlit_val(nat_shl(x, &y)),
            NatRed::Shr => self.mk_natlit_val(nat_shr(x, &y)),
            NatRed::Beq => self.bool_val(x == y),
            NatRed::Ble => self.bool_val(x <= y),
            NatRed::Succ => unreachable!(),
        }
    }

    fn mk_natlit_val(&mut self, n: BigUint) -> Option<V> {
        let p = self.ctx.alloc_bignum(n)?;
        Some(self.mk_natlit_hc(p))
    }

    fn bool_val(&mut self, b: bool) -> Option<V> {
        let cache = self.ctx.export_file.name_cache;
        let n = if b {
            cache.bool_true?
        } else {
            cache.bool_false?
        };
        let levels = self.ctx.alloc_levels(&[]);
        Some(self.mk_head_hc(RigidHead::Ctor(n, levels)))
    }

    pub(crate) fn value_has_free_bvar(&mut self, v: V) -> bool {
        self.vals().has_free_bvar(v)
    }

    pub(crate) fn value_to_bignum(&mut self, depth: u32, v: V) -> Option<BigUint> {
        self.value_to_bignum_at(depth, v, true)
    }

    pub(super) fn value_to_bignum_at(&mut self, depth: u32, v: V, deep: bool) -> Option<BigUint> {
        let mut succs: u64 = 0;
        let mut cur = v;
        loop {
            match self.val(cur) {
                Value::NatLit { lit, .. } => {
                    return Some(self.ctx.bignum(lit).clone() + succs);
                }
                Value::Rigid {
                    head: RigidHead::Ctor(name, _),
                    spine,
                    ..
                } => {
                    if Some(name) == self.ctx.export_file.name_cache.nat_zero
                        && self.vals().is_head(spine)
                    {
                        return Some(BigUint::from(succs));
                    }
                    if Some(name) == self.ctx.export_file.name_cache.nat_succ
                        && let Spine::Snoc { prev, elim, .. } = self.vals().spine(spine)
                        && self.vals().is_head(prev)
                        && let ElimView::App(a) = elim.view()
                    {
                        succs += 1;
                        cur = a;
                        continue;
                    }
                    return None;
                }
                Value::Unfold { head_value, .. } => {
                    if let Some(Value::NatLit { lit }) = self
                        .vals()
                        .step(head_value)
                        .filter(|&hv| hv != head_value)
                        .map(|hv| self.val(hv))
                    {
                        return Some(self.ctx.bignum(lit).clone() + succs);
                    }
                    if !deep {
                        return None;
                    }
                    return self.bignum_via_force(depth, cur).map(|n| n + succs);
                }
                Value::Rigid {
                    head: RigidHead::Recursor(..) | RigidHead::QuotConst(..),
                    ..
                } => {
                    if !deep {
                        return None;
                    }
                    return self.bignum_via_force(depth, cur).map(|n| n + succs);
                }
                _ => return None,
            }
        }
    }

    fn bignum_via_force(&mut self, depth: u32, v: V) -> Option<BigUint> {
        if self.value_has_free_bvar(v) {
            return None;
        }
        let f = self.force_all(depth, v);
        match self.val(f) {
            Value::NatLit { lit, .. } => Some(self.ctx.bignum(lit).clone()),
            Value::Rigid {
                head: RigidHead::Ctor(name, _),
                ..
            } if Some(name) == self.ctx.export_file.name_cache.nat_zero
                || Some(name) == self.ctx.export_file.name_cache.nat_succ =>
            {
                if f == v {
                    return None;
                }
                self.value_to_bignum(depth, f)
            }
            _ => None,
        }
    }
}
