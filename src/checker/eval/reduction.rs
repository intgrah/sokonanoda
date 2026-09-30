use crate::checker::cache::memo;
use crate::checker::env::{Declar, RecursorData};
use crate::checker::nat::{
    nat_div, nat_gcd, nat_land, nat_lor, nat_mod, nat_shl, nat_shr, nat_sub, nat_xor,
};
use crate::checker::tc::{NatBinOp, TypeChecker};
use crate::checker::value::{self, Elim, ElimView, RigidHead, S, Spine, V, Value};
use crate::outcome::reject;
use crate::term::ptr::{BigUintPtr, Id, LevelsPtr, NamePtr, StringPtr};
use num_bigint::BigUint;
use num_traits::pow::Pow;

type SpineArgs<'t> = smallvec::SmallVec<[V<'t>; 8]>;

enum ForceStep<'a> {
    Reduced(V<'a>),
    Descend(V<'a>),
    Done,
}

impl<'t> TypeChecker<'_, 't, '_> {
    pub(crate) fn ctor_shape(&mut self, name: NamePtr<'t>) -> Option<(u16, u16, NamePtr<'t>)> {
        self.env
            .get_constructor(&name)
            .map(|c| (c.num_params, c.num_fields, c.inductive_name))
    }

    pub(crate) fn can_be_struct_memo(&mut self, name: NamePtr<'t>) -> bool {
        self.env.can_be_struct(name)
    }

    pub(crate) fn do_proj(
        &mut self,
        depth: u32,
        ty_name: NamePtr<'t>,
        idx: u16,
        v: V<'t>,
    ) -> V<'t> {
        let v = self.whnf_head(depth, v);
        match v {
            Value::Rigid {
                head: RigidHead::Ctor(ctor_name, _),
                spine,
                ..
            } => {
                if let Some((num_params, _, inductive_name)) = self.ctor_shape(*ctor_name)
                    && inductive_name == ty_name
                {
                    let np = usize::from(num_params);
                    if let Some(ElimView::App(field)) =
                        spine.get(np + usize::from(idx)).map(Elim::view)
                    {
                        return self.force_thunk(depth, field);
                    }
                }
                self.proj_extend_spine(ty_name, idx, v)
            }
            Value::NatLit { ptr, .. } => {
                let ctor = self
                    .nat_lit_to_ctor_val(depth, *ptr)
                    .expect("do_proj: nat_lit_to_ctor_val failed");
                self.do_proj(depth, ty_name, idx, ctor)
            }
            Value::StrLit { ptr, .. } => {
                let ctor = self
                    .str_lit_to_ctor_val(depth, *ptr)
                    .expect("do_proj: str_lit_to_ctor_val failed");
                self.do_proj(depth, ty_name, idx, ctor)
            }
            Value::Rigid { .. } | Value::Unfold { .. } => self.proj_extend_spine(ty_name, idx, v),
            Value::Thunk { .. } => unreachable!("do_proj: Thunk after force_all"),
            _ => reject!("do_proj: not a neutral"),
        }
    }

    fn proj_extend_spine(&mut self, ty_name: NamePtr<'t>, idx: u16, v: V<'t>) -> V<'t> {
        match v {
            Value::Rigid { head, spine, .. } => {
                let (h, sp) = (*head, *spine);
                let ns = self.spine_snoc_hc(sp, Elim::proj(ty_name, idx));
                self.mk_rigid_hc(h, ns)
            }
            Value::Unfold {
                head,
                spine,
                head_value,
                ..
            } => {
                let (hn, hl, hv, sp) = (head.name, head.levels, *head_value, *spine);
                let ns = self.spine_snoc_hc(sp, Elim::proj(ty_name, idx));
                self.mk_unfold_hc(hn, hl, ns, hv)
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn proj_field_type_with(
        &mut self,
        depth: u32,
        struct_value: V<'t>,
        struct_ty: V<'t>,
        ty_name: NamePtr<'t>,
        idx: u16,
    ) -> Option<V<'t>> {
        let struct_ty = self.force_all(depth, struct_ty);
        let (ind_name, ind_levels, args) = match struct_ty {
            Value::Rigid {
                head: RigidHead::Inductive(n, ls),
                spine,
                ..
            } => {
                let aa = self.spine_apps(depth, spine)?;
                (*n, *ls, aa)
            }
            _ => return None,
        };
        if ind_name != ty_name {
            return None;
        }
        let ind = self.env.get_structure(ind_name, true)?;
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
                        let key = Id::of(rec_val);
                        if let Some(res) = self.fire_value(depth, rec_val, cur) {
                            self.tc_cache.iota_cache.insert(key, res);
                            steps += 1;
                            cur = res;
                            break;
                        }
                        self.tc_cache.iota_stuck.insert(key);
                        cur = rec_val;
                    }
                }
            }
        };
        self.note_whnf(depth, v, result, steps);
        result
    }

    fn iota_step(&mut self, depth: u32, v: V<'t>) -> ForceStep<'t> {
        let key = Id::of(v);
        if self.tc_cache.iota_stuck.contains(&key) {
            return ForceStep::Done;
        }
        if let Some(c) = self.tc_cache.iota_cache.get(&key) {
            return ForceStep::Reduced(c);
        }
        match v {
            Value::Rigid {
                head: RigidHead::Recursor(name, levels),
                spine,
                ..
            } => {
                let env = self.env;
                let Some(rec) = env.get_recursor(name) else {
                    return ForceStep::Done;
                };
                let Some(args) = self.spine_apps(depth, spine) else {
                    return ForceStep::Done;
                };
                if args.len() <= rec.major_idx() {
                    return ForceStep::Done;
                }
                if let Some(r) = self.k_pre_reduce(depth, rec, *levels, &args) {
                    self.tc_cache.iota_cache.insert(key, r);
                    return ForceStep::Reduced(r);
                }
                let major_h = self.strip_head(depth, args[rec.major_idx()]);
                if self.is_iota_reducible(major_h) {
                    return ForceStep::Descend(major_h);
                }
                if let Some(res) = self.fire_recursor(depth, rec, *levels, &args, major_h) {
                    self.tc_cache.iota_cache.insert(key, res);
                    ForceStep::Reduced(res)
                } else {
                    self.tc_cache.iota_stuck.insert(key);
                    ForceStep::Done
                }
            }
            Value::Rigid {
                head: RigidHead::QuotConst(name, _),
                spine,
                ..
            } => {
                let cache = self.ctx.export_file.name_cache;
                let qmk_pos = if Some(*name) == cache.quot_lift {
                    5
                } else if Some(*name) == cache.quot_ind {
                    4
                } else {
                    return ForceStep::Done;
                };
                let name = *name;
                let Some(args) = self.spine_apps(depth, spine) else {
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
                    self.tc_cache.iota_cache.insert(key, res);
                    ForceStep::Reduced(res)
                } else {
                    self.tc_cache.iota_stuck.insert(key);
                    ForceStep::Done
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
            Value::Rigid {
                head: RigidHead::Recursor(..),
                ..
            } => true,
            Value::Rigid {
                head: RigidHead::QuotConst(name, _),
                ..
            } => {
                let cache = self.ctx.export_file.name_cache;
                Some(*name) == cache.quot_lift || Some(*name) == cache.quot_ind
            }
            _ => false,
        }
    }

    fn fire_value(&mut self, depth: u32, rec_val: V<'t>, major: V<'t>) -> Option<V<'t>> {
        match rec_val {
            Value::Rigid {
                head: RigidHead::Recursor(name, levels),
                spine,
                ..
            } => {
                let env = self.env;
                let rec = env.get_recursor(name)?;
                let args = self.spine_apps(depth, spine)?;
                if args.len() <= rec.major_idx() {
                    return None;
                }
                self.fire_recursor(depth, rec, *levels, &args, major)
            }
            Value::Rigid {
                head: RigidHead::QuotConst(name, _),
                spine,
                ..
            } => {
                let args = self.spine_apps(depth, spine)?;
                self.fire_quot(depth, *name, &args, major)
            }
            _ => None,
        }
    }

    pub(crate) fn unfold_value(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        self.unfold_value_go(depth, v, false)
    }

    pub(crate) fn unfold_value_demand(&mut self, depth: u32, v: V<'t>) -> V<'t> {
        self.unfold_value_go(depth, v, self.tc_cache.probe_depth == 0)
    }

    fn unfold_value_go(&mut self, depth: u32, v: V<'t>, force: bool) -> V<'t> {
        if let Value::Unfold {
            head,
            spine,
            head_value,
            forced,
            ..
        } = v
        {
            if let Some(f) = forced.get() {
                return f;
            }
            if self.nat_extension
                && head.name.as_ref().is_nat_red()
                && let Some(args) = self.spine_apps(depth, spine)
            {
                if let Some(r) = self.do_nat_red(depth, head.name, &args) {
                    let _ = forced.set(r);
                    return r;
                }
                if !force && self.nat_red_defer(depth, head.name, &args) {
                    return v;
                }
            }
            let head_value = if let Some(&hv) = head_value.get() {
                hv
            } else {
                let Some(hv) = self.unfold_const(head.name, head.levels) else {
                    let _ = forced.set(v);
                    return v;
                };
                let _ = head_value.set(hv);
                hv
            };
            let spine = *spine;
            let mut cur = head_value;
            let mut run: SpineArgs<'t> = SpineArgs::new();
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
        let v_key = Id::of(v);
        if self.tc_cache.iota_stuck.contains(&v_key) {
            return None;
        }
        if let Some(cached) = self.tc_cache.iota_cache.get(&v_key) {
            return Some(*cached);
        }
        let result = match v {
            Value::Rigid {
                head: RigidHead::Recursor(name, levels),
                spine,
                ..
            } => {
                let args = self.spine_apps(depth, spine)?;
                self.do_recursor_iota(depth, *name, *levels, &args)
            }
            Value::Rigid {
                head: RigidHead::QuotConst(name, _),
                spine,
                ..
            } => {
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

    pub(crate) fn unfold_const(
        &mut self,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<V<'t>> {
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

    pub(crate) fn spine_apps(&mut self, depth: u32, spine: S<'t>) -> Option<SpineArgs<'t>> {
        let mut out = SpineArgs::with_capacity(spine.len() as usize);
        for elim in spine.elims_rev() {
            let ElimView::App(a) = elim.view() else {
                return None;
            };
            out.push(self.force_thunk(depth, a));
        }
        out.reverse();
        Some(out)
    }

    fn do_recursor_iota(
        &mut self,
        depth: u32,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
        args: &[V<'t>],
    ) -> Option<V<'t>> {
        let env = self.env;
        let rec = env.get_recursor(&name)?;
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
        rec: &RecursorData<'t>,
        levels: LevelsPtr<'t>,
        args: &[V<'t>],
    ) -> Option<V<'t>> {
        if !rec.is_k {
            return None;
        }
        let raw = self.force_thunk(depth, args[rec.major_idx()]);
        let kctor = self.try_k_reduce(depth, raw, rec)?;
        self.fire_recursor(depth, rec, levels, args, kctor)
    }

    pub(super) fn fire_recursor(
        &mut self,
        depth: u32,
        rec: &RecursorData<'t>,
        levels: LevelsPtr<'t>,
        args: &[V<'t>],
        major: V<'t>,
    ) -> Option<V<'t>> {
        if self.ctx.export_file.config.nat_extension
            && rec.all_inductives.first().copied() == self.ctx.export_file.name_cache.nat
            && let Value::NatLit { ptr, .. } = major
        {
            return Some(self.nat_rec_natlit(depth, args, *ptr, rec, levels));
        }
        let major = self
            .major_to_ctor(depth, major)
            .or_else(|| self.try_k_reduce(depth, major, rec))
            .or_else(|| self.try_struct_eta_reduce(depth, major, rec))
            .unwrap_or(major);
        let (ctor_name, ctor_args) = self.unwrap_ctor_app(depth, major)?;
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
        args: &[V<'t>],
        n_ptr: BigUintPtr<'t>,
        rec: &RecursorData<'t>,
        levels: LevelsPtr<'t>,
    ) -> V<'t> {
        use num_traits::Zero;
        let n = self
            .ctx
            .read_bignum(n_ptr)
            .expect("nat_rec_natlit: NatLit ptr")
            .clone();
        let nparams = usize::from(rec.num_params);
        let nmotives = usize::from(rec.num_motives);
        let major_idx = rec.major_idx();
        let zero_case = args[nparams + nmotives];
        let succ_case = self.force_thunk(depth, args[nparams + nmotives + 1]);
        let result = if n.is_zero() {
            zero_case
        } else {
            let pred = n - 1u8;
            let pred_ptr = self
                .ctx
                .alloc_bignum(pred)
                .expect("nat_rec_natlit: alloc pred");
            let pred_val = value::mk_natlit(self.arena, pred_ptr);
            let empty = self.empty_spine();
            let mut ih = value::mk_rigid_head_with_empty(
                self.arena,
                RigidHead::Recursor(rec.info.name, levels),
                empty,
            );
            for a in &args[..major_idx] {
                ih = self.apply(depth, ih, a);
            }
            ih = self.apply(depth, ih, pred_val);
            let stepped = self.apply(depth, succ_case, pred_val);
            self.apply(depth, stepped, ih)
        };
        self.apply_many(depth, result, &args[major_idx + 1..])
    }

    fn try_struct_eta_reduce(
        &mut self,
        depth: u32,
        major: V<'t>,
        rec: &RecursorData<'t>,
    ) -> Option<V<'t>> {
        if !matches!(major, Value::Rigid { .. } | Value::Unfold { .. }) {
            return None;
        }
        let rec_induct = self.ctx.get_major_induct(rec)?;
        if !self.can_be_struct_memo(rec_induct) {
            return None;
        }
        memo!(
            self.tc_cache.struct_eta_cache,
            (Id::of(major), rec_induct),
            self.try_struct_eta_reduce_uncached(depth, major, rec, rec_induct)
        )
    }

    fn try_struct_eta_reduce_uncached(
        &mut self,
        depth: u32,
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
        let mut new_ctor = value::mk_rigid_head_with_empty(
            self.arena,
            RigidHead::Ctor(ctor_name, ty_levels),
            self.empty_spine(),
        );
        for a in ty_args.iter().take(np).copied() {
            new_ctor = self.apply(depth, new_ctor, a);
        }
        for i in 0..num_fields {
            let proj = self.do_proj(depth, ty_name, i, major);
            new_ctor = self.apply(depth, new_ctor, proj);
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
            .map_or(0, |r| usize::from(r.ctor_telescope_size_wo_params));
        let take = (np + ctor_self).min(ty_args.len());
        let mut new_ctor = value::mk_rigid_head_with_empty(
            self.arena,
            RigidHead::Ctor(ctor_name, ty_levels),
            self.empty_spine(),
        );
        for a in ty_args.iter().take(take).copied() {
            new_ctor = self.apply(depth, new_ctor, a);
        }
        let new_ty = self.value_type(depth, new_ctor);
        if !self.conv_types_at(depth, major_ty_f, new_ty) {
            return None;
        }
        Some(new_ctor)
    }

    fn unwrap_inductive_app(
        &mut self,
        depth: u32,
        v: V<'t>,
    ) -> Option<(NamePtr<'t>, LevelsPtr<'t>, SpineArgs<'t>)> {
        match v {
            Value::Rigid {
                head: RigidHead::Inductive(n, ls),
                spine,
                ..
            } => {
                let args = self.spine_apps(depth, spine)?;
                Some((*n, *ls, args))
            }
            _ => None,
        }
    }

    fn major_to_ctor(&mut self, depth: u32, major: V<'t>) -> Option<V<'t>> {
        match major {
            Value::NatLit { ptr, .. } => self.nat_lit_to_ctor_val(depth, *ptr),
            Value::StrLit { ptr, .. } => self.str_lit_to_ctor_val(depth, *ptr),
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
        use num_traits::Zero;
        if !self.ctx.export_file.config.nat_extension {
            return None;
        }
        let nv = self.ctx.read_bignum(n)?.clone();
        let levels = self.ctx.alloc_levels_slice(&[]);
        let empty = self.empty_spine();
        if nv.is_zero() {
            let zero_name = self.ctx.export_file.name_cache.nat_zero?;
            Some(value::mk_rigid_head_with_empty(
                self.arena,
                RigidHead::Ctor(zero_name, levels),
                empty,
            ))
        } else {
            let pred = self.ctx.alloc_bignum(core::ops::Sub::sub(nv, 1u8))?;
            let pred_v = value::mk_natlit(self.arena, pred);
            let succ_name = self.ctx.export_file.name_cache.nat_succ?;
            let succ_v = value::mk_rigid_head_with_empty(
                self.arena,
                RigidHead::Ctor(succ_name, levels),
                empty,
            );
            Some(self.apply(depth, succ_v, pred_v))
        }
    }

    fn unwrap_ctor_app(&mut self, depth: u32, v: V<'t>) -> Option<(NamePtr<'t>, SpineArgs<'t>)> {
        match v {
            Value::Rigid {
                head: RigidHead::Ctor(name, _),
                spine,
                ..
            } => {
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

    pub(super) fn fire_quot(
        &mut self,
        depth: u32,
        c_name: NamePtr<'t>,
        args: &[V<'t>],
        qmk: V<'t>,
    ) -> Option<V<'t>> {
        let cache = self.ctx.export_file.name_cache;
        let rest_idx = if Some(c_name) == cache.quot_lift {
            6usize
        } else if Some(c_name) == cache.quot_ind {
            5usize
        } else {
            return None;
        };
        let (qmk_head, qmk_spine) = match qmk {
            Value::Rigid {
                head: RigidHead::QuotConst(name, _),
                spine,
                ..
            } => (*name, *spine),
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
        let result = self.apply(depth, f, last);
        Some(self.apply_many(depth, result, &args[rest_idx..]))
    }

    fn do_nat_red(&mut self, depth: u32, name: NamePtr<'t>, args: &[V<'t>]) -> Option<V<'t>> {
        self.do_nat_red_at(depth, name, args, true)
    }

    pub(super) fn do_nat_red_shallow(
        &mut self,
        depth: u32,
        name: NamePtr<'t>,
        args: &[V<'t>],
    ) -> Option<V<'t>> {
        self.do_nat_red_at(depth, name, args, false)
    }

    fn do_nat_red_at(
        &mut self,
        depth: u32,
        name: NamePtr<'t>,
        args: &[V<'t>],
        deep: bool,
    ) -> Option<V<'t>> {
        use crate::term::name::NatRed;
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
            let op = if let NatRed::DivGo = kind {
                NatBinOp::Div
            } else {
                NatBinOp::Mod
            };
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
        use NatBinOp::{Add, Beq, Ble, Div, Gcd, LAnd, LOr, Mod, Mul, Pow, Shl, Shr, Sub, XOr};
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
            Shl => self.mk_natlit_val(nat_shl(x, &y)),
            Shr => self.mk_natlit_val(nat_shr(x, &y)),
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
        let n = if b {
            cache.bool_true?
        } else {
            cache.bool_false?
        };
        let levels = self.ctx.alloc_levels_slice(&[]);
        Some(value::mk_rigid_head_with_empty(
            self.arena,
            RigidHead::Ctor(n, levels),
            self.empty_spine(),
        ))
    }

    pub(crate) fn value_has_free_bvar(&mut self, depth: u32, v: V<'t>) -> bool {
        let v = self.force_thunk(depth, v);
        memo!(
            self.tc_cache.fvar_cache,
            Id::of(v),
            match v {
                Value::Sort { .. }
                | Value::NatLit { .. }
                | Value::StrLit { .. }
                | Value::Lam { .. }
                | Value::Pi { .. } => false,
                Value::Rigid {
                    head: RigidHead::BVar(..),
                    ..
                } => true,
                Value::Rigid { spine, .. } | Value::Unfold { spine, .. } => {
                    spine.elims_rev().any(|elim| {
                        matches!(elim.view(), ElimView::App(a) if self.value_has_free_bvar(depth, a))
                    })
                }
                Value::Thunk { .. } => unreachable!("force_thunk left a Thunk"),
            }
        )
    }

    pub(crate) fn value_to_bignum(&mut self, depth: u32, v: V<'t>) -> Option<BigUint> {
        self.value_to_bignum_at(depth, v, true)
    }

    pub(super) fn value_to_bignum_at(
        &mut self,
        depth: u32,
        v: V<'t>,
        deep: bool,
    ) -> Option<BigUint> {
        let mut succs: u64 = 0;
        let mut cur = self.force_thunk(depth, v);
        loop {
            match cur {
                Value::NatLit { ptr, .. } => {
                    return self.ctx.read_bignum(*ptr).cloned().map(|n| n + succs);
                }
                Value::Rigid {
                    head: RigidHead::Ctor(name, _),
                    spine,
                    ..
                } => {
                    if Some(*name) == self.ctx.export_file.name_cache.nat_zero && spine.is_empty() {
                        return Some(BigUint::from(succs));
                    }
                    if Some(*name) == self.ctx.export_file.name_cache.nat_succ
                        && let Spine::Snoc {
                            prev: Spine::Empty,
                            elim,
                            ..
                        } = spine
                        && let ElimView::App(a) = elim.view()
                    {
                        succs += 1;
                        cur = self.force_thunk(depth, a);
                        continue;
                    }
                    return None;
                }
                Value::Unfold { head_value, .. } => {
                    if let Some(Value::NatLit { ptr, .. }) = head_value.get() {
                        return self.ctx.read_bignum(*ptr).cloned().map(|n| n + succs);
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

    fn bignum_via_force(&mut self, depth: u32, v: V<'t>) -> Option<BigUint> {
        if self.value_has_free_bvar(depth, v) {
            return None;
        }
        let f = self.force_all(depth, v);
        match f {
            Value::NatLit { ptr, .. } => self.ctx.read_bignum(*ptr).cloned(),
            Value::Rigid {
                head: RigidHead::Ctor(name, _),
                ..
            } if Some(*name) == self.ctx.export_file.name_cache.nat_zero
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
