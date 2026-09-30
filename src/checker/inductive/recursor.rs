use super::{CtorHeader, InductiveCheckState};
use crate::checker::env::{Declar, DeclarInfo, RecRule, RecursorData};
use crate::checker::tc::TypeChecker;
use crate::checker::value::{V, Value};
use crate::outcome::{ensure, ensure_eq, reject};
use crate::term::ptr::{ExprPtr, NamePtr};
use std::sync::Arc;

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub(super) fn mk_majors(&mut self, st: &mut InductiveCheckState<'t>) {
        for (idx, ind_const) in st.ind_consts.iter().copied().enumerate() {
            let num_indices =
                u16::try_from(st.local_indices[idx].len()).expect("index count exceeds u16");
            let param_vars = self.param_vars(st, num_indices);
            let index_vars: Vec<ExprPtr<'t>> = (0..num_indices)
                .map(|k| self.ctx.mk_var(num_indices - 1 - k))
                .collect();
            let mut ty = self.ctx.foldl_apps(ind_const, param_vars.into_iter());
            ty = self.ctx.foldl_apps(ty, index_vars.into_iter());
            st.majors.push(ty);
        }
    }
    fn mk_motive_dep(&mut self, st: &InductiveCheckState<'t>, ind_type_idx: usize) -> ExprPtr<'t> {
        let elim_sort = self.ctx.mk_sort(st.elim_level.unwrap());
        let major = st.majors[ind_type_idx];
        let w_major = self.ctx.mk_pi(major, elim_sort);
        let indices = st.local_indices[ind_type_idx].clone();
        self.mk_pis_dep(indices.as_slice(), 0, w_major)
    }
    pub(super) fn mk_motives(&mut self, st: &mut InductiveCheckState<'t>) {
        debug_assert_eq!(st.local_indices.len(), st.ind_consts.len());
        debug_assert_eq!(st.majors.len(), st.ind_consts.len());
        for i in 0..st.ind_consts.len() {
            st.motives.push(self.mk_motive_dep(st, i));
        }
    }
    fn is_rec_argument_v(
        &mut self,
        st: &InductiveCheckState<'t>,
        cursor: V<'t>,
        depth0: u32,
    ) -> Option<usize> {
        let mut depth = depth0;
        let mut cur = cursor;
        while let Some(Value::Pi { domain, body, .. }) = self.force_pi(depth, cur) {
            let domain = *domain;
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
        }
        self.which_valid_ind_app_v(st, depth, cur)
    }
    fn handle_rec_args_aux(
        &mut self,
        cursor: V<'t>,
        depth0: u32,
    ) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>, V<'t>, u32) {
        let mut depth = depth0;
        let mut cur = cursor;
        let mut xs = Vec::new();
        while let Some(Value::Pi { domain, body, .. }) = self.force_pi(depth, cur) {
            let domain = *domain;
            let dom_e = self.quote(depth, domain);
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
            xs.push(dom_e);
        }
        let cur = self.force_all(depth, cur);
        let end = self.quote_weak(depth, cur);
        (end, xs, cur, depth)
    }
    fn sep_nonrec_rec_ctor_args(
        &mut self,
        st: &InductiveCheckState<'t>,
        ctor_type_cursor: ExprPtr<'t>,
        depth0: u32,
    ) -> (
        ExprPtr<'t>,
        V<'t>,
        u32,
        Vec<ExprPtr<'t>>,
        Vec<(usize, V<'t>)>,
    ) {
        let mut all_args: Vec<ExprPtr<'t>> = Vec::new();
        let mut rec_positions = Vec::new();
        self.tc_cache.clear();
        let mut depth = depth0;
        let mut cur = self.value_of(ctor_type_cursor);
        for i in 0..st.local_params.len() {
            let Value::Pi { domain, body, .. } = cur else {
                reject!("constructor type has fewer binders than the block parameters")
            };
            let domain = *domain;
            let lv = self.mk_bvar_hc(
                u32::try_from(i).expect("parameter count exceeds u32"),
                domain,
            );
            cur = self.apply_closure(depth, body, lv, Some(domain));
        }
        while let Value::Pi { domain, body, .. } = cur {
            let domain = *domain;
            let binder_type = self.quote(depth, domain);
            let is_rec = self.is_rec_argument_v(st, domain, depth).is_some();
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            if is_rec {
                rec_positions.push((all_args.len(), domain));
            }
            all_args.push(binder_type);
            depth += 1;
        }
        let end = self.quote(depth, cur);
        (end, cur, depth, all_args, rec_positions)
    }
    fn handle_rec_args_minor(
        &mut self,
        st: &InductiveCheckState<'t>,
        rec_args: &[(usize, V<'t>)],
        ctor_args_base: u32,
        base_depth: u32,
    ) -> Vec<ExprPtr<'t>> {
        let mut out = Vec::new();
        for (i, (pos, dom_v)) in rec_args.iter().copied().enumerate() {
            self.tc_cache.clear();
            let here = base_depth + u32::try_from(i).expect("too many recursive arguments");
            let (arg_ty, xs, arg_v, arg_depth) = self.handle_rec_args_aux(dom_v, here);
            let (ind_ty_idx, applied_indices) = self.get_i_indices_at(st, arg_ty, arg_v, arg_depth);
            let n = u16::try_from(xs.len()).expect("telescope exceeds u16");
            let total = u16::try_from(arg_depth).expect("depth exceeds u16");
            let motive_level =
                u16::try_from(ind_ty_idx).expect("motive count exceeds u16") + st.num_params();
            let motive = self.ctx.mk_var(total - 1 - motive_level);
            let arg_level = u16::try_from(ctor_args_base).expect("depth exceeds u16")
                + u16::try_from(pos).expect("position exceeds u16");
            let x_vars: Vec<ExprPtr<'t>> = (0..n).map(|j| self.ctx.mk_var(n - 1 - j)).collect();
            let rec_arg_var = self.ctx.mk_var(total - 1 - arg_level);
            let motive_base = {
                let lhs = self
                    .ctx
                    .foldl_apps(motive, applied_indices.into_iter().rev());
                let u_app = self.ctx.foldl_apps(rec_arg_var, x_vars.iter().copied());
                self.ctx.mk_app(lhs, u_app)
            };
            let v_i_ty = self.mk_pis_dep(xs.as_slice(), 0, motive_base);
            out.push(v_i_ty);
        }
        out
    }
    fn mk_minors1group(
        &mut self,
        st: &InductiveCheckState<'t>,
        ctors: &[CtorHeader<'t>],
    ) -> Vec<ExprPtr<'t>> {
        let mut out = Vec::new();
        let base = u32::from(st.minor_base());
        for ctor in ctors.iter().copied() {
            let (stripd, stripd_v, args_depth, all_ctor_args, rec_ctor_args) =
                self.sep_nonrec_rec_ctor_args(st, ctor.ty, base);
            let (ind_ty_idx, applied_indices) =
                self.get_i_indices_at(st, stripd, stripd_v, args_depth);
            let v = self.handle_rec_args_minor(st, rec_ctor_args.as_slice(), base, args_depth);
            let n_args = u16::try_from(all_ctor_args.len()).expect("telescope exceeds u16");
            let n_v = u16::try_from(v.len()).expect("telescope exceeds u16");
            let total = u16::try_from(args_depth).expect("depth exceeds u16") + n_v;
            let motive_level =
                u16::try_from(ind_ty_idx).expect("motive count exceeds u16") + st.num_params();
            let motive = self.ctx.mk_var(total - 1 - motive_level);
            let arg_vars: Vec<ExprPtr<'t>> = (0..n_args)
                .map(|j| self.ctx.mk_var(total - 1 - (st.minor_base() + j)))
                .collect();
            let param_vars = self.param_vars(st, total - st.num_params());
            let c_app0 = {
                let rhs = self.ctx.mk_const(ctor.name, st.uparams);
                let rhs = self.ctx.foldl_apps(rhs, param_vars.into_iter());
                self.ctx.foldl_apps(rhs, arg_vars.iter().copied())
            };
            let shifted_indices: Vec<ExprPtr<'t>> = applied_indices
                .into_iter()
                .map(|e| self.ctx.lift(e, 0, n_v))
                .collect();
            let c_app = self
                .ctx
                .foldl_apps(motive, shifted_indices.into_iter().rev());
            let c_app = self.ctx.mk_app(c_app, c_app0);

            let minor_type = self.mk_pis_dep(v.as_slice(), 0, c_app);
            let minor_type = self.mk_pis_dep(all_ctor_args.as_slice(), 0, minor_type);
            out.push(minor_type);
        }
        out
    }
    pub(super) fn mk_minors(&mut self, st: &mut InductiveCheckState<'t>) {
        assert_eq!(
            st.all_inductives_incl_specialized.len(),
            st.ind_consts.len()
        );
        for ind_ty in &st.all_inductives_incl_specialized {
            st.minors
                .push(self.mk_minors1group(st, ind_ty.ctors.as_slice()));
        }
    }
    fn handle_rec_ctor_args_rec_rule(
        &mut self,
        st: &InductiveCheckState<'t>,
        rec_args: &[(usize, V<'t>)],
        ctor_args_base: u32,
        base_depth: u32,
    ) -> Vec<ExprPtr<'t>> {
        let mut out = Vec::new();
        let num_minors = u16::try_from(st.minors.iter().map(std::vec::Vec::len).sum::<usize>())
            .expect("too many minors");
        let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
        for (pos, dom_v) in rec_args.iter().copied() {
            self.tc_cache.clear();
            let (u_i_ty, xs, u_i_v, u_i_depth) = self.handle_rec_args_aux(dom_v, base_depth);
            let (it_idx, applied_indices) = self.get_i_indices_at(st, u_i_ty, u_i_v, u_i_depth);
            let it_name = st
                .all_inductives_incl_specialized
                .get(it_idx)
                .map(|x| x.name)
                .unwrap();
            let rec_name = self.ctx.str(it_name, rec_str_ptr);
            let rec_app = self.ctx.mk_const(rec_name, st.rec_uparams.unwrap());
            let n = u16::try_from(xs.len()).expect("telescope exceeds u16");
            let total = u16::try_from(u_i_depth).expect("depth exceeds u16");
            let param_vars = self.param_vars(st, total - st.num_params());
            let motive_vars: Vec<ExprPtr<'t>> = (0..st.num_motives())
                .map(|j| self.ctx.mk_var(total - 1 - (st.num_params() + j)))
                .collect();
            let minor_vars: Vec<ExprPtr<'t>> = (0..num_minors)
                .map(|k| self.ctx.mk_var(total - 1 - (st.minor_base() + k)))
                .collect();
            let app = self.ctx.foldl_apps(rec_app, param_vars.into_iter());
            let app = self.ctx.foldl_apps(app, motive_vars.into_iter());
            let app = self.ctx.foldl_apps(app, minor_vars.into_iter());
            let app = self
                .ctx
                .foldl_apps(app, applied_indices.iter().copied().rev());
            let arg_level = u16::try_from(ctor_args_base).expect("depth exceeds u16")
                + u16::try_from(pos).expect("position exceeds u16");
            let x_vars: Vec<ExprPtr<'t>> = (0..n).map(|j| self.ctx.mk_var(n - 1 - j)).collect();
            let rec_arg_var = self.ctx.mk_var(total - 1 - arg_level);
            let app_rhs = self.ctx.foldl_apps(rec_arg_var, x_vars.iter().copied());
            let app = self.ctx.mk_app(app, app_rhs);
            out.push(self.mk_lambdas_dep(xs.as_slice(), 0, app));
        }
        out
    }
    fn mk_rec_rule1(
        &mut self,
        st: &InductiveCheckState<'t>,
        ctor: CtorHeader<'t>,
        flat_mapped_minors: &[ExprPtr<'t>],
        minor_idx: u16,
    ) -> RecRule<'t> {
        let num_minors = u16::try_from(flat_mapped_minors.len()).expect("too many minors");
        let ctor_args_base = u32::from(st.minor_base() + num_minors);
        let (_, _, args_depth, all_ctor_args, rec_ctor_args) =
            self.sep_nonrec_rec_ctor_args(st, ctor.ty, ctor_args_base);
        let handled_rec_args = self.handle_rec_ctor_args_rec_rule(
            st,
            rec_ctor_args.as_slice(),
            ctor_args_base,
            args_depth,
        );
        let n_args = u16::try_from(all_ctor_args.len()).expect("telescope exceeds u16");
        let total = u16::try_from(args_depth).expect("depth exceeds u16");
        let arg_vars: Vec<ExprPtr<'t>> = (0..n_args)
            .map(|j| self.ctx.mk_var(n_args - 1 - j))
            .collect();
        let this_minor = self.ctx.mk_var(total - 1 - (st.minor_base() + minor_idx));
        let comp_rhs = self.ctx.foldl_apps(this_minor, arg_vars.iter().copied());
        let comp_rhs = self
            .ctx
            .foldl_apps(comp_rhs, handled_rec_args.iter().copied());
        let comp_rhs = self.mk_lambdas_dep(all_ctor_args.as_slice(), 0, comp_rhs);
        let comp_rhs = self.mk_lambdas_flat(flat_mapped_minors, comp_rhs);
        let motives = st.motives.clone();
        let comp_rhs = self.mk_lambdas_flat(motives.as_slice(), comp_rhs);
        let params = st.local_params.clone();
        let comp_rhs = self.mk_lambdas_dep(params.as_slice(), 0, comp_rhs);
        let num_fields = ctor.ty.pi_telescope_size() as usize - st.local_params.len();
        RecRule {
            ctor_name: ctor.name,
            ctor_telescope_size_wo_params: u16::try_from(num_fields).unwrap(),
            val: comp_rhs,
        }
    }
    fn mk_rec_rule_lhs(
        &mut self,
        st: &InductiveCheckState<'t>,
        rec_name: NamePtr<'t>,
        ctor: CtorHeader<'t>,
        flat_mapped_minors: &[ExprPtr<'t>],
    ) -> ExprPtr<'t> {
        let num_minors = u16::try_from(flat_mapped_minors.len()).expect("too many minors");
        let ctor_args_base = u32::from(st.minor_base() + num_minors);
        let (ind_ty_app, ind_ty_v, args_depth, all_ctor_args, _) =
            self.sep_nonrec_rec_ctor_args(st, ctor.ty, ctor_args_base);
        let (ind_ty_idx, applied_indices) =
            self.get_i_indices_at(st, ind_ty_app, ind_ty_v, args_depth);
        let expected_rec_name = {
            let rec = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
            self.ctx
                .str(st.all_inductives_incl_specialized[ind_ty_idx].name, rec)
        };
        ensure_eq!(
            rec_name,
            expected_rec_name,
            "computation rule belongs to the wrong recursor"
        );

        let n_args = u16::try_from(all_ctor_args.len()).expect("telescope exceeds u16");
        let total = u16::try_from(args_depth).expect("depth exceeds u16");
        let param_vars = self.param_vars(st, total - st.num_params());
        let motive_vars: Vec<_> = (0..st.num_motives())
            .map(|i| self.ctx.mk_var(total - 1 - (st.num_params() + i)))
            .collect();
        let minor_vars: Vec<_> = (0..num_minors)
            .map(|i| self.ctx.mk_var(total - 1 - (st.minor_base() + i)))
            .collect();
        let arg_vars: Vec<_> = (0..n_args)
            .map(|i| self.ctx.mk_var(n_args - 1 - i))
            .collect();

        let ctor_app = self.ctx.mk_const(ctor.name, st.uparams);
        let ctor_app = self.ctx.foldl_apps(ctor_app, param_vars.iter().copied());
        let ctor_app = self.ctx.foldl_apps(ctor_app, arg_vars.iter().copied());
        let lhs = self.ctx.mk_const(rec_name, st.rec_uparams.unwrap());
        let lhs = self.ctx.foldl_apps(lhs, param_vars.into_iter());
        let lhs = self.ctx.foldl_apps(lhs, motive_vars.into_iter());
        let lhs = self.ctx.foldl_apps(lhs, minor_vars.into_iter());
        let lhs = self.ctx.foldl_apps(lhs, applied_indices.into_iter().rev());
        let lhs = self.ctx.mk_app(lhs, ctor_app);
        let lhs = self.mk_lambdas_dep(all_ctor_args.as_slice(), 0, lhs);
        let lhs = self.mk_lambdas_flat(flat_mapped_minors, lhs);
        let lhs = self.mk_lambdas_flat(st.motives.as_slice(), lhs);
        self.mk_lambdas_dep(st.local_params.as_slice(), 0, lhs)
    }
    pub(super) fn check_generated_recursors(
        &mut self,
        st: &InductiveCheckState<'t>,
        recursors: &[Declar<'t>],
    ) {
        let minors = st.flat_minors();
        assert_eq!(recursors.len(), st.all_inductives_incl_specialized.len());
        for (recursor, ind) in recursors
            .iter()
            .zip(st.all_inductives_incl_specialized.iter())
        {
            self.tc_cache.clear();
            self.check_declar_info_v(recursor);
            let Declar::Recursor(recursor) = recursor else {
                panic!("expected generated recursor")
            };
            assert_eq!(recursor.rec_rules.len(), ind.ctors.len());
            for (rule, ctor) in recursor.rec_rules.iter().zip(ind.ctors.iter().copied()) {
                assert_eq!(rule.ctor_name, ctor.name);
                let expected_fields = ctor.ty.pi_telescope_size() - st.num_params();
                assert_eq!(rule.ctor_telescope_size_wo_params, expected_fields);
                let lhs = self.mk_rec_rule_lhs(st, recursor.info.name, ctor, minors.as_slice());
                self.tc_cache.clear();
                let lhs_ty = self.infer_value(
                    crate::checker::tc::InferFlag::Check,
                    0,
                    self.empty_env(),
                    self.empty_ctx(),
                    lhs,
                );
                let rhs_ty = self.infer_value(
                    crate::checker::tc::InferFlag::Check,
                    0,
                    self.empty_env(),
                    self.empty_ctx(),
                    rule.val,
                );
                ensure!(
                    self.conv_types_at(0, lhs_ty, rhs_ty),
                    "generated recursor computation rule is not type-preserving"
                );
            }
        }
    }
    fn mk_rec_rules(&mut self, st: &InductiveCheckState<'t>) -> Vec<Vec<RecRule<'t>>> {
        let minors = st.flat_minors();
        let mut overall_ctor_idx = 0u16;
        st.all_inductives_incl_specialized
            .iter()
            .map(|ind_ty| {
                ind_ty
                    .ctors
                    .iter()
                    .map(|&ctor| {
                        let rec_rule =
                            self.mk_rec_rule1(st, ctor, minors.as_slice(), overall_ctor_idx);
                        overall_ctor_idx += 1;
                        rec_rule
                    })
                    .collect()
            })
            .collect()
    }
    fn mk_recursor_aux(
        &mut self,
        st: &InductiveCheckState<'t>,
        ind_name: NamePtr<'t>,
        motive_idx: u16,
        major: ExprPtr<'t>,
        local_indices: &[ExprPtr<'t>],
        flat_mapped_minors: &[ExprPtr<'t>],
        rec_rules: &[RecRule<'t>],
    ) -> Declar<'t> {
        let num_indices = u16::try_from(local_indices.len()).expect("index count exceeds u16");
        let num_minors = u16::try_from(flat_mapped_minors.len()).expect("too many minors");
        let gap = st.num_motives() + num_minors;
        let total = st.minor_base() + num_minors + num_indices + 1;

        let motive = self.ctx.mk_var(total - 1 - (st.num_params() + motive_idx));
        let index_vars: Vec<ExprPtr<'t>> = (0..num_indices)
            .map(|k| {
                self.ctx
                    .mk_var(total - 1 - (st.minor_base() + num_minors + k))
            })
            .collect();
        let major_var = self.ctx.mk_var(0);
        let motive_app_base = self.ctx.foldl_apps(motive, index_vars.into_iter());
        let motive_app = self.ctx.mk_app(motive_app_base, major_var);

        let major_ty = self.ctx.lift(major, num_indices, gap);
        let rec_ty = self.ctx.mk_pi(major_ty, motive_app);
        let rec_ty = self.mk_pis_dep(local_indices, gap, rec_ty);
        let rec_ty = self.mk_pis_flat(flat_mapped_minors, rec_ty);
        let motives = st.motives.clone();
        let rec_ty = self.mk_pis_flat(motives.as_slice(), rec_ty);
        let params = st.local_params.clone();
        let rec_ty = self.mk_pis_dep(params.as_slice(), 0, rec_ty);

        let recursor = RecursorData {
            info: DeclarInfo {
                name: {
                    let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
                    self.ctx.str(ind_name, rec_str_ptr)
                },
                uparams: st.rec_uparams.unwrap(),
                ty: rec_ty,
            },
            all_inductives: Arc::from(
                st.all_inductives_incl_specialized
                    .iter()
                    .map(|x| x.name)
                    .collect::<Vec<_>>(),
            ),
            num_params: u16::try_from(st.local_params.len()).unwrap(),
            num_indices: u16::try_from(local_indices.len()).unwrap(),
            num_motives: u16::try_from(st.motives.len()).unwrap(),
            num_minors: u16::try_from(flat_mapped_minors.len()).unwrap(),
            rec_rules: Arc::from(rec_rules),
            is_k: st.k_target.unwrap(),
        };

        Declar::Recursor(recursor)
    }
    pub(crate) fn mk_recursors(&mut self, st: &InductiveCheckState<'t>) -> Vec<Declar<'t>> {
        let rec_rules = self.mk_rec_rules(st);
        let mut recursors = Vec::new();
        for (i, ind) in st.all_inductives_incl_specialized.iter().enumerate() {
            let major = st.majors[i];
            let local_indices = st.local_indices.get(i).unwrap();
            let minors = st.flat_minors();
            let recursor = self.mk_recursor_aux(
                st,
                ind.name,
                u16::try_from(i).expect("motive count exceeds u16"),
                major,
                local_indices,
                minors.as_slice(),
                rec_rules[i].as_slice(),
            );
            recursors.push(recursor);
        }
        recursors
    }
}
