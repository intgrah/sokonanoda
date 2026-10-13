// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use super::InductiveCheckState;
use crate::checker::cache::memo;
use crate::checker::context::TcCtx;
use crate::checker::tc::TypeChecker;
use crate::checker::value::{Closure, EMPTY_ENV, ElimView, RigidHead, S, V, Value};
use crate::outcome::{ensure, reject};
use crate::term::expr::Expr::{App, Const, Lambda, Let, NatLit, Pi, Proj, Sort, StringLit, Var};
use crate::term::id::{ExprId, LevelsId, NameId};

impl<'x, 't: 'x> TypeChecker<'x, 't> {
    fn check_positivity1(&mut self, st: &InductiveCheckState, cursor: V, depth0: u32) {
        let mut depth = depth0;
        let mut cur = cursor;
        loop {
            cur = self.force_all(depth, cur);
            if !self.value_has_ind_occ(depth, cur, st.ind_consts.as_ref()) {
                return;
            }
            let Value::Pi { domain, body, .. } = self.val(cur) else {
                // We only need to know that it's a valid ind-app for SOMETHING in the block, since
                // this is only a binder in the constructor, not the end of the telescope.
                ensure!(self.which_valid_ind_app_v(st, depth, cur).is_some());
                return;
            };
            let (domain, body) = (domain, body);
            ensure!(
                !self.value_has_ind_occ(depth, domain, st.ind_consts.as_ref()),
                "non-positive occurrence"
            );
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
        }
    }
    pub(super) fn get_i_indices_at(
        &mut self,
        st: &InductiveCheckState,
        ind_ty_app: ExprId,
        v: V,
        depth: u32,
    ) -> (usize, Vec<ExprId>) {
        let valid_app_idx = self.which_valid_ind_app_v(st, depth, v).unwrap();
        let (_, ctor_args_wo_params) = self.ctx.unfold_apps_rev(ind_ty_app);
        // Compensate for stack-like unfold
        let keep = ctor_args_wo_params
            .len()
            .saturating_sub(st.local_params.len());
        (valid_app_idx, ctor_args_wo_params[..keep].to_vec())
    }
    pub(super) fn inst_params_at(
        &mut self,
        e: ExprId,
        num_params: usize,
        depth: u16,
    ) -> ExprId {
        let n = u16::try_from(num_params).expect("parameter count exceeds u16");
        let substs: Vec<ExprId> = (0..n).map(|j| self.ctx.mk_var(depth + n - 1 - j)).collect();
        self.ctx.inst_open(e, substs.as_slice())
    }
    fn value_has_ind_occ(&mut self, depth: u32, v: V, haystack: &[ExprId]) -> bool {
        memo!(
            self.tc_cache.ind_occ_cache,
            v,
            match self.val(v) {
                Value::Sort { .. } | Value::NatLit { .. } | Value::StrLit { .. } => false,
                Value::Rigid { head, spine, .. } => {
                    let head_hit = match head {
                        RigidHead::BVar(_, ty) => self.value_has_ind_occ(depth, ty, haystack),
                        RigidHead::Axiom(n, _)
                        | RigidHead::Ctor(n, _)
                        | RigidHead::Recursor(n, _)
                        | RigidHead::QuotConst(n, _)
                        | RigidHead::Inductive(n, _) => name_is_ind_occ(self.ctx, n, haystack),
                    };
                    head_hit || self.spine_has_ind_occ(depth, spine, haystack)
                }
                Value::Unfold { head, spine, .. } => {
                    name_is_ind_occ(self.ctx, head.name, haystack)
                        || self.spine_has_ind_occ(depth, spine, haystack)
                }
                Value::Lam { body, .. } => {
                    let dom = self.lam_domain(depth, v);
                    let body = body;
                    self.value_has_ind_occ(depth, dom, haystack)
                        || self.closure_has_ind_occ(depth, &body, haystack)
                }
                Value::Pi { domain, body, .. } => {
                    let (domain, body) = (domain, body);
                    self.value_has_ind_occ(depth, domain, haystack)
                        || self.closure_has_ind_occ(depth, &body, haystack)
                }
            }
        )
    }
    fn spine_has_ind_occ(&mut self, depth: u32, spine: S, haystack: &[ExprId]) -> bool {
        let elims = self.vals().spine_to_vec(spine);
        elims.iter().rev().any(|elim| {
            matches!(elim.view(), ElimView::App(a) if self.value_has_ind_occ(depth, a, haystack))
        })
    }
    fn closure_has_ind_occ(
        &mut self,
        depth: u32,
        clo: &Closure,
        haystack: &[ExprId],
    ) -> bool {
        if has_ind_occ(self.ctx, clo.body, haystack) {
            return true;
        }
        let nlb = clo.loose;
        let mask = self.ctx.mask(clo.body);
        for idx in 1..nlb {
            if (mask >> idx.min(63)) & 1 == 0 {
                continue;
            }
            if let Some(slot) = self.vals().env_lookup(clo.env, idx - 1)
                && self.value_has_ind_occ(depth, slot, haystack)
            {
                return true;
            }
        }
        false
    }
    fn is_bvar_at(&self, v: V, level: u32) -> bool {
        matches!(self.val(v), Value::Rigid { head: RigidHead::BVar(l, _), spine } if l == level && self.vals().is_head(spine))
    }
    pub(super) fn which_valid_ind_app_v(
        &mut self,
        st: &InductiveCheckState,
        depth: u32,
        v: V,
    ) -> Option<usize> {
        let f = self.force_all(depth, v);
        let (name, levels, spine) = match self.val(f) {
            Value::Rigid {
                head: RigidHead::Inductive(n, ls),
                spine,
                ..
            } => (n, ls, spine),
            _ => return None,
        };
        let pos = st
            .ind_consts
            .iter()
            .copied()
            .position(|x| match self.ctx.ex(x) {
                Const { name: n, .. } => n == name,
                _ => panic!(),
            })?;
        let Const {
            levels: expected_levels,
            ..
        } = self.ctx.ex(st.ind_consts[pos])
        else {
            return None;
        };
        if !self.ctx.eq_antisymm_many(levels, expected_levels) {
            return None;
        }
        let num_params = st.local_params.len();
        if self.vals().spine_len(spine) as usize != num_params + st.local_indices[pos].len() {
            return None;
        }
        let args = self.vals().spine_apps(spine)?;
        for i in 0..num_params {
            if !self.is_bvar_at(
                args[i],
                u32::try_from(i).expect("parameter count exceeds u32"),
            ) {
                return None;
            }
        }
        for ix in &args[num_params..] {
            if self.value_has_ind_occ(depth, *ix, &st.ind_consts) {
                return None;
            }
        }
        Some(pos)
    }
    fn is_valid_ind_app_v(
        &mut self,
        st: &InductiveCheckState,
        parent_ind_name: NameId,
        depth: u32,
        v: V,
    ) -> bool {
        let f = self.force_all(depth, v);
        let name = match self.val(f) {
            Value::Rigid {
                head: RigidHead::Inductive(n, _),
                ..
            } => n,
            _ => return false,
        };
        name == parent_ind_name && self.which_valid_ind_app_v(st, depth, f).is_some()
    }
    pub(crate) fn check_ctor(
        &mut self,
        st: &InductiveCheckState,
        parent_ind_name: NameId,
        ctor_type_cursor: ExprId,
    ) {
        self.tc_cache.clear();
        let mut depth = 0u32;
        let mut env = EMPTY_ENV;
        let mut cur = self.value_of(ctor_type_cursor);
        for i in 0..st.local_params.len() {
            let Value::Pi { domain, body, .. } = self.val(cur) else {
                reject!("constructor type has fewer binders than the block parameters")
            };
            let domain = domain;
            let expected = self.eval(depth, env, st.local_params[i]);
            ensure!(self.def_eq_at(depth, domain, expected), "def_eq failed");
            let fresh = self.mk_bvar_hc(depth, domain);
            env = self.env_extend(env, fresh);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
        }
        // Non-param constructor args.
        while let Value::Pi { domain, body, .. } = self.val(cur) {
            let domain = domain;
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

pub(super) fn name_is_ind_occ(ctx: &TcCtx<'_>, n: NameId, haystack: &[ExprId]) -> bool {
    haystack.iter().copied().any(|c| match ctx.ex(c) {
        Const { name, .. } => name == n,
        _ => panic!(),
    })
}
pub(super) fn check_uniform_inductive_occurrences(
    ctx: &TcCtx<'_>,
    e: ExprId,
    ind_names: &[NameId],
    expected_levels: LevelsId,
    num_params: u16,
) {
    check_uniform_inductive_occurrences_at(ctx, e, ind_names, expected_levels, num_params, 0);
}
fn check_uniform_inductive_occurrences_at(
    ctx: &TcCtx<'_>,
    e: ExprId,
    ind_names: &[NameId],
    expected_levels: LevelsId,
    num_params: u16,
    offset: u16,
) {
    let mut head = e;
    let mut args_rev = Vec::new();
    while let App { fun, arg } = ctx.ex(head) {
        args_rev.push(arg);
        head = fun;
    }
    if let Const { name, levels } = ctx.ex(head)
        && ind_names.contains(&name)
        && args_rev.len() <= usize::from(num_params)
    {
        let levels_match = ctx.levels(levels) == ctx.levels(expected_levels);
        let params_match = args_rev.len() == usize::from(num_params)
            && offset >= num_params
            && args_rev.iter().rev().enumerate().all(|(i, &arg)| {
                matches!(
                    ctx.ex(arg),
                    Var { dbj_idx } if usize::from(dbj_idx) == usize::from(offset) - 1 - i
                )
            });
        ensure!(
            levels_match && params_match,
            "inductive occurrence is not applied uniformly to the block parameters and universe levels"
        );
        return;
    }

    match ctx.ex(e) {
        Var { .. } | Sort { .. } | Const { .. } | NatLit { .. } | StringLit { .. } => {}
        App { fun, arg } => {
            check_uniform_inductive_occurrences_at(
                ctx,
                fun,
                ind_names,
                expected_levels,
                num_params,
                offset,
            );
            check_uniform_inductive_occurrences_at(
                ctx,
                arg,
                ind_names,
                expected_levels,
                num_params,
                offset,
            );
        }
        Pi { binder_type, body } | Lambda { binder_type, body } => {
            check_uniform_inductive_occurrences_at(
                ctx,
                binder_type,
                ind_names,
                expected_levels,
                num_params,
                offset,
            );
            check_uniform_inductive_occurrences_at(
                ctx,
                body,
                ind_names,
                expected_levels,
                num_params,
                offset.checked_add(1).expect("binder depth exceeds u16"),
            );
        }
        Let {
            binder_type,
            val,
            body,
            ..
        } => {
            check_uniform_inductive_occurrences_at(
                ctx,
                binder_type,
                ind_names,
                expected_levels,
                num_params,
                offset,
            );
            check_uniform_inductive_occurrences_at(
                ctx,
                val,
                ind_names,
                expected_levels,
                num_params,
                offset,
            );
            check_uniform_inductive_occurrences_at(
                ctx,
                body,
                ind_names,
                expected_levels,
                num_params,
                offset.checked_add(1).expect("binder depth exceeds u16"),
            );
        }
        Proj { structure, .. } => check_uniform_inductive_occurrences_at(
            ctx,
            structure,
            ind_names,
            expected_levels,
            num_params,
            offset,
        ),
    }
}
pub(super) fn has_ind_occ(ctx: &TcCtx<'_>, e: ExprId, haystack: &[ExprId]) -> bool {
    let f = |nptr| {
        haystack.iter().copied().any(|c| match ctx.ex(c) {
            Const { name, .. } => name == nptr,
            _ => panic!(),
        })
    };

    ctx.find_const(e, f)
}
