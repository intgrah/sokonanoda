// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use super::InductiveCheckState;
use crate::checker::cache::memo;
use crate::checker::tc::TypeChecker;
use crate::checker::value::{Closure, ElimView, RigidHead, S, V, Value};
use crate::outcome::{ensure, reject};
use crate::term::expr::Expr::{App, Const, Lambda, Let, NatLit, Pi, Proj, Sort, StringLit, Var};
use crate::term::ptr::{ExprPtr, Id, LevelsPtr, NamePtr};

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    fn check_positivity1(&mut self, st: &InductiveCheckState<'t>, cursor: V<'t>, depth0: u32) {
        let mut depth = depth0;
        let mut cur = cursor;
        loop {
            cur = self.force_all(depth, cur);
            if !self.value_has_ind_occ(depth, cur, st.ind_consts.as_ref()) {
                return;
            }
            let Value::Pi { domain, body, .. } = cur else {
                // We only need to know that it's a valid ind-app for SOMETHING in the block, since
                // this is only a binder in the constructor, not the end of the telescope.
                ensure!(self.which_valid_ind_app_v(st, depth, cur).is_some());
                return;
            };
            let (domain, body) = (*domain, *body);
            ensure!(
                !self.value_has_ind_occ(depth, domain, st.ind_consts.as_ref()),
                "non-positive occurrence"
            );
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, &body, fresh, Some(domain));
            depth += 1;
        }
    }
    pub(super) fn get_i_indices_at(
        &mut self,
        st: &InductiveCheckState<'t>,
        ind_ty_app: ExprPtr<'t>,
        v: V<'t>,
        depth: u32,
    ) -> (usize, Vec<ExprPtr<'t>>) {
        let valid_app_idx = self.which_valid_ind_app_v(st, depth, v).unwrap();
        let (_, ctor_args_wo_params) = ind_ty_app.unfold_apps_stack(self.arena);
        // Compensate for stack-like unfold
        let keep = ctor_args_wo_params
            .len()
            .saturating_sub(st.local_params.len());
        (valid_app_idx, ctor_args_wo_params[..keep].to_vec())
    }
    pub(super) fn inst_params_at(
        &mut self,
        e: ExprPtr<'t>,
        num_params: usize,
        depth: u16,
    ) -> ExprPtr<'t> {
        let n = u16::try_from(num_params).expect("parameter count exceeds u16");
        let substs: Vec<ExprPtr<'t>> = (0..n).map(|j| self.ctx.mk_var(depth + n - 1 - j)).collect();
        self.ctx.inst_open(e, substs.as_slice())
    }
    fn value_has_ind_occ(&mut self, depth: u32, v: V<'t>, haystack: &[ExprPtr<'t>]) -> bool {
        memo!(
            self.tc_cache.ind_occ_cache,
            Id::of(v),
            match v {
                Value::Sort { .. } | Value::NatLit { .. } | Value::StrLit { .. } => false,
                Value::Rigid { head, spine, .. } => {
                    let head_hit = match *head {
                        RigidHead::BVar(_, ty) => self.value_has_ind_occ(depth, ty, haystack),
                        RigidHead::Axiom(n, _)
                        | RigidHead::Ctor(n, _)
                        | RigidHead::Recursor(n, _)
                        | RigidHead::QuotConst(n, _)
                        | RigidHead::Inductive(n, _) => name_is_ind_occ(n, haystack),
                    };
                    head_hit || self.spine_has_ind_occ(depth, spine, haystack)
                }
                Value::Unfold { head, spine, .. } => {
                    name_is_ind_occ(head.name, haystack)
                        || self.spine_has_ind_occ(depth, spine, haystack)
                }
                Value::Lam { body, .. } => {
                    let dom = self.lam_domain(depth, v);
                    let body = *body;
                    self.value_has_ind_occ(depth, dom, haystack)
                        || self.closure_has_ind_occ(depth, &body, haystack)
                }
                Value::Pi { domain, body, .. } => {
                    let (domain, body) = (*domain, *body);
                    self.value_has_ind_occ(depth, domain, haystack)
                        || self.closure_has_ind_occ(depth, &body, haystack)
                }
            }
        )
    }
    fn spine_has_ind_occ(&mut self, depth: u32, spine: S<'t>, haystack: &[ExprPtr<'t>]) -> bool {
        spine.elims_rev().any(|elim| {
            matches!(elim.view(), ElimView::App(a) if self.value_has_ind_occ(depth, a, haystack))
        })
    }
    fn closure_has_ind_occ(
        &mut self,
        depth: u32,
        clo: &Closure<'t>,
        haystack: &[ExprPtr<'t>],
    ) -> bool {
        if has_ind_occ(clo.body, haystack) {
            return true;
        }
        let nlb = clo.body.num_loose_bvars();
        let mask = clo.body.as_ref().fv_mask();
        for idx in 0..nlb {
            if idx < 64 && (mask >> idx) & 1 == 0 {
                continue;
            }
            if let Some(slot) = clo.env.lookup(idx)
                && self.value_has_ind_occ(depth, slot, haystack)
            {
                return true;
            }
        }
        false
    }
    fn is_bvar_at(v: V<'t>, level: u32) -> bool {
        matches!(v, Value::Rigid { head: RigidHead::BVar(l, _), spine, .. } if *l == level && spine.is_empty())
    }
    pub(super) fn which_valid_ind_app_v(
        &mut self,
        st: &InductiveCheckState<'t>,
        depth: u32,
        v: V<'t>,
    ) -> Option<usize> {
        let f = self.force_all(depth, v);
        let (name, levels, spine) = match f {
            Value::Rigid {
                head: RigidHead::Inductive(n, ls),
                spine,
                ..
            } => (*n, *ls, *spine),
            _ => return None,
        };
        let pos = st.ind_consts.iter().copied().position(|x| match *x {
            Const { name: n, .. } => n == name,
            _ => panic!(),
        })?;
        let Const {
            levels: expected_levels,
            ..
        } = *st.ind_consts[pos]
        else {
            return None;
        };
        if !self.ctx.eq_antisymm_many(levels, expected_levels) {
            return None;
        }
        let num_params = st.local_params.len();
        if spine.len() as usize != num_params + st.local_indices[pos].len() {
            return None;
        }
        let args = spine.apps()?;
        for i in 0..num_params {
            if !Self::is_bvar_at(
                args[i],
                u32::try_from(i).expect("parameter count exceeds u32"),
            ) {
                return None;
            }
        }
        for ix in &args[num_params..] {
            if self.value_has_ind_occ(depth, ix, &st.ind_consts) {
                return None;
            }
        }
        Some(pos)
    }
    fn is_valid_ind_app_v(
        &mut self,
        st: &InductiveCheckState<'t>,
        parent_ind_name: NamePtr<'t>,
        depth: u32,
        v: V<'t>,
    ) -> bool {
        let f = self.force_all(depth, v);
        let name = match f {
            Value::Rigid {
                head: RigidHead::Inductive(n, _),
                ..
            } => *n,
            _ => return false,
        };
        name == parent_ind_name && self.which_valid_ind_app_v(st, depth, f).is_some()
    }
    pub(crate) fn check_ctor(
        &mut self,
        st: &InductiveCheckState<'t>,
        parent_ind_name: NamePtr<'t>,
        ctor_type_cursor: ExprPtr<'t>,
    ) {
        self.tc_cache.clear();
        let mut depth = 0u32;
        let mut env = self.empty_env();
        let mut cur = self.value_of(ctor_type_cursor);
        for i in 0..st.local_params.len() {
            let Value::Pi { domain, body, .. } = cur else {
                reject!("constructor type has fewer binders than the block parameters")
            };
            let domain = *domain;
            let expected = self.eval(depth, env, st.local_params[i]);
            ensure!(self.def_eq_at(depth, domain, expected), "def_eq failed");
            let fresh = self.mk_bvar_hc(depth, domain);
            env = self.env_extend(env, fresh);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
        }
        // Non-param constructor args.
        while let Value::Pi { domain, body, .. } = cur {
            let domain = *domain;
            let s = self
                .level_of_type(depth, domain)
                .expect("constructor argument is not a type");
            // The inductive being constructed either has to be a `Prop`,
            // or the constructor argument's type has to be <= the inductive's
            // type.
            ensure!(
                st.is_zero.unwrap() || self.ctx.leq(s, st.block_codom.unwrap()),
                "Constructor argument was too large for the corresponding inductive type"
            );

            // Assert that there are no non-positive occurrences in the constructor.
            self.check_positivity1(st, domain, depth);
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
        }
        // The end of the constructor has to be of the form `parentIndConst params* indices*`
        // as in `List A` or `Nat.le x y`
        ensure!(self.is_valid_ind_app_v(st, parent_ind_name, depth, cur));
    }
}

pub(super) fn name_is_ind_occ<'t>(n: NamePtr<'t>, haystack: &[ExprPtr<'t>]) -> bool {
    haystack.iter().copied().any(|c| match *c {
        Const { name, .. } => name == n,
        _ => panic!(),
    })
}
pub(super) fn check_uniform_inductive_occurrences<'t>(
    e: ExprPtr<'t>,
    ind_names: &[NamePtr<'t>],
    expected_levels: LevelsPtr<'t>,
    num_params: u16,
) {
    check_uniform_inductive_occurrences_at(e, ind_names, expected_levels, num_params, 0);
}
fn check_uniform_inductive_occurrences_at<'t>(
    e: ExprPtr<'t>,
    ind_names: &[NamePtr<'t>],
    expected_levels: LevelsPtr<'t>,
    num_params: u16,
    offset: u16,
) {
    let mut head = e;
    let mut args_rev = Vec::new();
    while let App { fun, arg, .. } = *head {
        args_rev.push(arg);
        head = fun;
    }
    if let Const { name, levels, .. } = *head
        && ind_names.contains(&name)
        && args_rev.len() <= usize::from(num_params)
    {
        let levels_match = levels.as_ref() == expected_levels.as_ref();
        let params_match = args_rev.len() == usize::from(num_params)
            && offset >= num_params
            && args_rev.iter().rev().enumerate().all(|(i, arg)| {
                matches!(
                    **arg,
                    Var { dbj_idx, .. } if usize::from(dbj_idx) == usize::from(offset) - 1 - i
                )
            });
        ensure!(
            levels_match && params_match,
            "inductive occurrence is not applied uniformly to the block parameters and universe levels"
        );
        return;
    }

    match *e {
        Var { .. } | Sort { .. } | Const { .. } | NatLit { .. } | StringLit { .. } => {}
        App { fun, arg, .. } => {
            check_uniform_inductive_occurrences_at(
                fun,
                ind_names,
                expected_levels,
                num_params,
                offset,
            );
            check_uniform_inductive_occurrences_at(
                arg,
                ind_names,
                expected_levels,
                num_params,
                offset,
            );
        }
        Pi {
            binder_type, body, ..
        }
        | Lambda {
            binder_type, body, ..
        } => {
            check_uniform_inductive_occurrences_at(
                binder_type,
                ind_names,
                expected_levels,
                num_params,
                offset,
            );
            check_uniform_inductive_occurrences_at(
                body,
                ind_names,
                expected_levels,
                num_params,
                offset.checked_add(1).expect("binder depth exceeds u16"),
            );
        }
        Let { data, .. } => {
            check_uniform_inductive_occurrences_at(
                data.binder_type,
                ind_names,
                expected_levels,
                num_params,
                offset,
            );
            check_uniform_inductive_occurrences_at(
                data.val,
                ind_names,
                expected_levels,
                num_params,
                offset,
            );
            check_uniform_inductive_occurrences_at(
                data.body,
                ind_names,
                expected_levels,
                num_params,
                offset.checked_add(1).expect("binder depth exceeds u16"),
            );
        }
        Proj { structure, .. } => check_uniform_inductive_occurrences_at(
            structure,
            ind_names,
            expected_levels,
            num_params,
            offset,
        ),
    }
}
pub(super) fn has_ind_occ<'t>(e: ExprPtr<'t>, haystack: &[ExprPtr<'t>]) -> bool {
    let f = |nptr| {
        haystack.iter().copied().any(|c| match *c {
            Const { name, .. } => name == nptr,
            _ => panic!(),
        })
    };

    e.find_const(f)
}
