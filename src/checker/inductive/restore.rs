// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use super::{IndTyHeader, InductiveCheckState};
use crate::checker::env::{
    ConstructorData, Declar, DeclarInfo, InductiveData, RecRule, RecursorData,
};
use crate::checker::tc::TypeChecker;
use crate::checker::value::Value;
use crate::outcome::{ensure, ensure_eq, reject};
use crate::term::expr::Expr::{App, Const, Lambda, Let, NatLit, Pi, Proj, Sort, StringLit, Var};
use crate::term::hash::FxIndexMap;
use crate::term::ptr::{ExprPtr, LevelsPtr, NamePtr};
use std::sync::Arc;

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub(super) fn assert_nonnested_tys_def_eq(
        &mut self,
        base_ind: &InductiveData<'t>,
        st: &InductiveCheckState<'t>,
    ) {
        assert!(!st.is_nested());
        for name in base_ind.all_ind_names.iter() {
            match (
                self.env.get_old_declar(*name),
                self.env.get_temp_declar(*name),
            ) {
                (Some(Declar::Inductive(old)), Some(Declar::Inductive(new))) => {
                    ensure!(old.aux_data_ck(new));
                    debug_assert!(!std::ptr::eq(old, new));
                    self.tc_cache.clear();
                    self.assert_def_eq(old.info.ty, new.info.ty);
                }
                _ => reject!("expected an inductive declaration"),
            }
        }
    }
    pub(super) fn assert_nonnested_ctors_def_eq(&mut self, st: &InductiveCheckState<'t>) {
        assert!(!st.is_nested());
        for inductive in &st.all_inductives_incl_specialized {
            for ctor in &inductive.ctors {
                match (
                    self.env.get_old_declar(ctor.name),
                    self.env.get_temp_declar(ctor.name),
                ) {
                    (Some(Declar::Constructor(old)), Some(Declar::Constructor(new))) => {
                        ensure!(old.aux_data_ck(new));
                        debug_assert!(!std::ptr::eq(old, new));
                        self.tc_cache.clear();
                        self.assert_def_eq(old.info.ty, new.info.ty);
                    }
                    _ => reject!("expected an inductive declaration"),
                }
            }
        }
    }
    fn assert_nonnested_rec_rule_def_eq(
        &mut self,
        st: &InductiveCheckState<'t>,
        old: LevelsPtr<'t>,
        imported_rr: &RecRule<'t>,
        constructed_rr: &RecRule<'t>,
    ) {
        assert!(!std::ptr::eq(imported_rr, constructed_rr));
        // Should be structurally != because they come from different envs.
        assert_ne!(imported_rr, constructed_rr);
        assert!(!st.is_nested());
        self.tc_cache.clear();
        ensure_eq!(imported_rr.ctor_name, constructed_rr.ctor_name);
        ensure_eq!(
            imported_rr.ctor_telescope_size_wo_params,
            constructed_rr.ctor_telescope_size_wo_params
        );
        let rr_made_val =
            self.ctx
                .subst_expr_levels(constructed_rr.val, st.rec_uparams.unwrap(), old);
        self.assert_imported_expr_matches(imported_rr.val, rr_made_val);
    }
    pub(super) fn assert_nonnested_recursors_def_eq(
        &mut self,
        st: &InductiveCheckState<'t>,
        recursors: &Vec<Declar<'t>>,
    ) {
        assert!(!st.is_nested());
        for new_rec in recursors {
            match (self.env.get_old_declar(new_rec.info().name), new_rec) {
                (
                    Some(
                        old @ Declar::Recursor(
                            old_r @ RecursorData {
                                rec_rules: old_rec_rules,
                                ..
                            },
                        ),
                    ),
                    new @ Declar::Recursor(
                        new_r @ RecursorData {
                            rec_rules: new_rec_rules,
                            ..
                        },
                    ),
                ) => {
                    self.tc_cache.clear();
                    ensure!(old_r.aux_data_ck(new_r));
                    assert!(!std::ptr::eq(old, new));
                    // Should be structurally != because they come from different envs.
                    assert_ne!(old, new);
                    let imported_w_new_uparams = self.ctx.subst_expr_levels(
                        old.info().ty,
                        old.info().uparams,
                        st.rec_uparams.unwrap(),
                    );
                    self.assert_def_eq(imported_w_new_uparams, new.info().ty);
                    ensure_eq!(old_rec_rules.len(), new_rec_rules.len());
                    for (r_old, r_new) in old_rec_rules.iter().zip(new_rec_rules.iter()) {
                        self.assert_nonnested_rec_rule_def_eq(st, old.info().uparams, r_old, r_new);
                    }
                }
                _ => reject!("Expected (Declar::Recursor, Declar::Recursor)"),
            }
        }
    }
    /// Return an ordered map, mapping the specialized recursor names to the
    /// unspecialized recursor names. For example:
    ///
    /// ```ignore
    /// specialized_rec_name_to_unspecialized_rec_name := [
    ///     _nested.Array_1.rec                  |-> Lean.Elab.Term.Do.Code.rec_1
    ///     _nested.List_2.rec                   |-> Lean.Elab.Term.Do.Code.rec_2
    ///     _nested.Lean.Elab.Term.Do.Alt_3.rec  |-> Lean.Elab.Term.Do.Code.rec_3
    /// ]
    /// ```
    fn mk_specialized_rec_to_unspecialized_map(
        &mut self,
        base_mutuals: &[IndTyHeader<'t>],
    ) -> FxIndexMap<NamePtr<'t>, NamePtr<'t>> {
        // The unmodified name of the "main" type being checked, e.g. `Lean.Syntax`
        let main_ind_ty_name = base_mutuals.first().map(|zth| zth.name).unwrap();
        let mut specialized_rec_names_to_unspecialized_rec_names =
            crate::term::hash::new_fx_index_map();
        let rec_str = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));

        // The MODIFIED version looked up in the new environment. The modification would
        // just be additions to `all_ind_names`, which now contains the `_nested.Array`
        // specialized type names.
        let InductiveData { all_ind_names, .. } = self.env.get_inductive(main_ind_ty_name).unwrap();
        // The modified inductive with the specialized names added must have more elements
        // than the unmodified type's list of names.
        assert!(all_ind_names.len() > base_mutuals.len());
        // For every NEW NESTED elem (new, because we skip `n_types`, skipping all of the base mutuals.)
        // For each modified e.g. `_nested..` name
        for ind_name in all_ind_names.iter().copied().skip(base_mutuals.len()) {
            let specialized_rec_name = self.ctx.str(ind_name, rec_str);
            let unspecialized_rec_name = self.ctx.str(main_ind_ty_name, rec_str);
            let unspecialized_rec_name = self.ctx.append_index_after(
                unspecialized_rec_name,
                (specialized_rec_names_to_unspecialized_rec_names.len() + 1) as u64,
            );
            specialized_rec_names_to_unspecialized_rec_names
                .insert(specialized_rec_name, unspecialized_rec_name);
        }
        specialized_rec_names_to_unspecialized_rec_names
    }
    /// From `X.mk`, return the un-specialized version of that type, and the
    /// parent inductive name for the constructor
    ///
    /// This looks up the constructor *in the new environment*, so the parent ind name
    /// might be modified, or it might not be. E.g. you might get `Lean.Syntax`, or
    /// you might get `_nested.Array_1`
    fn get_nested_if_aux_ctor(
        &mut self,
        st: &InductiveCheckState<'t>,
        c: NamePtr<'t>,
    ) -> Option<(ExprPtr<'t>, NamePtr<'t>)> {
        // `inductive_name`
        let ConstructorData { inductive_name, .. } = self.env.get_constructor(c)?;
        let unspecialized_ty = st.nested_to_unspecialized_ty.get(inductive_name).copied()?;
        Some((unspecialized_ty, *inductive_name))
    }
    /// If `c` is `_nested_Array_1.mk`, return just `Array.mk`,
    ///
    /// This is only used in restoring recursor rules, since those hold the constructor name.
    fn restore_ctor_name(
        &mut self,
        st: &InductiveCheckState<'t>,
        ctor_name: NamePtr<'t>,
    ) -> NamePtr<'t> {
        // from `_nested_Array_1.mk`, retrieve `(Array Lean.Syntax, _nested.Array_1)`
        let (unspecialized_ty, base_ind_name) = self.get_nested_if_aux_ctor(st, ctor_name).unwrap();
        // Now get just `Const(Array, [])`
        let unspecialized_f = unspecialized_ty.unfold_apps_fun();
        // Get just the name for `Array`
        let (unspecialized_ty_name, ..) = unspecialized_f.try_const_info().unwrap();
        // Replace ctor_name[specialized_name |-> unspecialized_name]
        // e.g. `_nested.Array_1.mk |-> Array.mk`
        self.ctx
            .replace_pfx(ctor_name, base_ind_name, unspecialized_ty_name)
    }
    fn restore_replace(
        &mut self,
        e: ExprPtr<'t>,
        num_params: usize,
        depth: u16,
        st: &InductiveCheckState<'t>,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) -> ExprPtr<'t> {
        match self.replace_f(
            e,
            num_params,
            depth,
            st,
            specialized_rec_names_to_unspecialized_rec_names,
        ) {
            Some(out) => out,
            None => match *e {
                Var { .. } | Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => e,
                Lambda {
                    binder_type, body, ..
                } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        num_params,
                        depth,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let body = self.restore_replace(
                        body,
                        num_params,
                        depth + 1,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    self.ctx.mk_lambda(binder_type, body)
                }
                Pi {
                    binder_type, body, ..
                } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        num_params,
                        depth,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let body = self.restore_replace(
                        body,
                        num_params,
                        depth + 1,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    self.ctx.mk_pi(binder_type, body)
                }
                Let {
                    data:
                        &crate::term::expr::LetData {
                            binder_type,
                            val,
                            body,
                            nondep,
                        },
                    ..
                } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        num_params,
                        depth,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let val = self.restore_replace(
                        val,
                        num_params,
                        depth,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let body = self.restore_replace(
                        body,
                        num_params,
                        depth + 1,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    self.ctx.mk_let(binder_type, val, body, nondep)
                }
                Proj {
                    ty_name,
                    idx,
                    structure,
                    ..
                } => {
                    let structure = self.restore_replace(
                        structure,
                        num_params,
                        depth,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    self.ctx.mk_proj(ty_name, idx, structure)
                }
                App { fun, arg, .. } => {
                    let fun = self.restore_replace(
                        fun,
                        num_params,
                        depth,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let arg = self.restore_replace(
                        arg,
                        num_params,
                        depth,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    self.ctx.mk_app(fun, arg)
                }
            },
        }
    }
    /// Traverse an expression replacing one of three appearances:\
    /// 1. `_nested.Array_N`     |-> `Array T`\
    /// 2. `_nested.Array_N.mk`  |-> `Array.mk`\
    /// 3. `_nested.Array_N.rec` |-> `BaseType.rec_N`\
    ///
    /// Gets a map of the specialized recursors tot he "permanent" recursors:
    ///
    /// (`_nested.Array_1.rec`, `Lean.Syntax.rec_1`)\
    /// (`_nested.List_2.rec`, `Lean.Syntax.rec_2`)
    fn replace_f(
        &mut self,
        e: ExprPtr<'t>,
        num_params: usize,
        depth: u16,
        st: &InductiveCheckState<'t>,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) -> Option<ExprPtr<'t>> {
        // If it's a recursor application, update the recursor.
        // e.g.
        // replacing(1) const _nested.Lean.PersistentArrayNode_2.rec with Lean.Elab.InfoTree.rec_2
        // replacing(1) const _nested.List_6.rec with Lean.Elab.InfoTree.rec_6
        if let Const { name, levels, .. } = *e {
            // If e was `Const(_nested.Array_1.rec)`, return `Const(Lean.Syntax.rec_1)`
            if let Some(rec_name) = specialized_rec_names_to_unspecialized_rec_names.get(&name) {
                return Some(self.ctx.mk_const(*rec_name, levels));
            }
        }
        let (_, c_name, _, e_args) = e.unfold_const_apps(self.arena)?;
        // If it's an application of e.g. `_nested_Array1`, update
        // Replace one of the specialized types with the un-specialized version:
        // e.g.
        //
        // replacing(2) const _nested.Lean.PersistentArrayNode_2 with Lean.PersistentArrayNode.{0} Lean.Elab.InfoTree
        // replacing(2) const _nested.List_6 with List.{0} (Lean.PersistentArrayNode.{0} Lean.Elab.InfoTree)
        //
        // aux2nested elem := (_nested.Array_1, (Array.[0] Lean.Syntax.[]))
        // aux2nested elem := (_nested.List_2, (List.[0] Lean.Syntax.[]))
        if let Some(nested) = st.nested_to_unspecialized_ty.get(&c_name) {
            debug_assert!(e_args.len() >= st.num_params as usize);
            let nested = *nested;
            let inner = self.inst_params_at(nested, num_params, depth);
            let outer = self
                .ctx
                .foldl_apps(inner, e_args.iter().copied().skip(st.num_params as usize));
            return Some(outer);
        }
        let (nested_no_inst, aux_i_name) = self.get_nested_if_aux_ctor(st, c_name)?;

        debug_assert!(e_args.len() >= st.num_params as usize);
        let nested_inst = self.inst_params_at(nested_no_inst, num_params, depth);
        let (nested_f, i_args) = nested_inst.unfold_apps(self.arena);
        // Replace one of the nested constructor applications with a regular ctor application.
        //
        // replacing(3) c := _nested.Array_3.mk, auxI_name := _nested.Array_3, I_c := Array, c' := Array.mk.{0}
        // replacing(3) c := _nested.List_4.nil, auxI_name := _nested.List_4, I_c := List, c' := List.nil.{0}
        match *nested_f {
            Const {
                name: i_name,
                levels,
                ..
            } => {
                let cprime_name = self.ctx.replace_pfx(c_name, aux_i_name, i_name);
                let cprime = self.ctx.mk_const(cprime_name, levels);
                let inner = self.ctx.foldl_apps(cprime, i_args.iter().copied());
                let outer = self
                    .ctx
                    .foldl_apps(inner, e_args.iter().copied().skip(st.num_params as usize));
                Some(outer)
            }
            _ => panic!("Should be const"),
        }
    }
    /// Restore a single expression (can be a type or value)
    fn restore_e(
        &mut self,
        st: &InductiveCheckState<'t>,
        e: ExprPtr<'t>,
        nested_rec_name_to_rec_name: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) -> ExprPtr<'t> {
        let is_pi = matches!(*e, Pi { .. });
        let num_params = st.local_params.len();
        let mut cur = self.value_of(e);
        let mut binders: Vec<ExprPtr<'t>> = Vec::with_capacity(num_params);
        for level in 0..num_params {
            let depth = u32::try_from(level).expect("parameter count exceeds u32");
            let f = cur;
            let dom = match f {
                Value::Pi { domain, .. } => *domain,
                // Also match on Lambda for restoring recursor rules.
                Value::Lam { .. } => self.lam_domain(depth, f),
                _ => reject!("malformed recursor"),
            };
            let dom_e = self.quote(depth, dom);
            let fresh = self.mk_bvar_hc(depth, dom);
            cur = match f {
                Value::Pi { body, .. } => self.apply_closure(depth + 1, body, fresh, Some(dom)),
                Value::Lam { body, .. } => self.apply_closure(depth + 1, body, fresh, None),
                _ => unreachable!(),
            };
            binders.push(dom_e);
        }
        let body_depth = u32::try_from(num_params).expect("parameter count exceeds u32");
        let body = self.quote(body_depth, cur);
        let mut out = self.restore_replace(body, num_params, 0, st, nested_rec_name_to_rec_name);
        while let Some(dom_e) = binders.pop() {
            out = if is_pi {
                self.ctx.mk_pi(dom_e, out)
            } else {
                self.ctx.mk_lambda(dom_e, out)
            };
        }
        out
    }
    fn restore_recursor1(
        &mut self,
        st: &InductiveCheckState<'t>,
        // The list of names in the mutual block, NOT including
        // the temporary nested declarations.
        all_ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
        // This map holds the specialized nested elements' recursor names;
        // e.g. `_nested.Array_1.rec |-> Lean.Syntax.rec_1`,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        // `rec_name` This can be either an old/base inductive rec name, or a fresh/specialized name
        // Either `Syntax.rec`, or `_nested.Array_N.rec`
        rec_name: NamePtr<'t>,
    ) -> RecursorData<'t> {
        // resolve e.g. `_nested.Array_1.rec` to `Lean.Syntax.rec_1`
        let resolved_rec_name = specialized_rec_names_to_unspecialized_rec_names
            .get(&rec_name)
            .copied()
            .unwrap_or(rec_name);
        // The new environment's recursor for this type; e.g. the recursor
        // that's in the environment for _nested.Array_1.rec
        let new_env_rec @ RecursorData { .. } = self.env.get_recursor(rec_name).cloned().unwrap();
        let restored_ty = self.restore_e(
            st,
            new_env_rec.info.ty,
            specialized_rec_names_to_unspecialized_rec_names,
        );
        let rules: Arc<[RecRule<'t>]> = new_env_rec
            .rec_rules
            .iter()
            .map(|&rule| {
                let val = self.restore_e(
                    st,
                    rule.val,
                    specialized_rec_names_to_unspecialized_rec_names,
                );
                let ctor_name = if rec_name == resolved_rec_name {
                    rule.ctor_name
                } else {
                    self.restore_ctor_name(st, rule.ctor_name)
                };
                RecRule {
                    ctor_name,
                    val,
                    ..rule
                }
            })
            .collect();
        RecursorData {
            info: DeclarInfo {
                name: resolved_rec_name,
                ty: restored_ty,
                ..new_env_rec.info
            },
            all_inductives: all_ind_names_no_specialized.clone(),
            rec_rules: rules,
            ..new_env_rec
        }
    }
    fn check_restored_recursor1(
        &mut self,
        st: &InductiveCheckState<'t>,
        // The list of names in the mutual block, NOT including
        // the temporary nested declarations.
        ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
        nested_rec_name_to_rec_name: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        rec_name: NamePtr<'t>,
    ) {
        let restored = self.restore_recursor1(
            st,
            ind_names_no_specialized,
            nested_rec_name_to_rec_name,
            rec_name,
        );
        let resolved_rec_name = nested_rec_name_to_rec_name
            .get(&rec_name)
            .copied()
            .unwrap_or(rec_name);
        match self.env.get_old_declar(resolved_rec_name) {
            Some(Declar::Recursor(original @ RecursorData { .. })) => {
                ensure!(original.aux_data_ck(&restored));
                self.tc_cache.clear();
                self.assert_def_eq(original.info.ty, restored.info.ty);
                // have to do the rec rules as well.
                ensure_eq!(original.rec_rules.len(), restored.rec_rules.len());
                for (&old, &new) in original.rec_rules.iter().zip(restored.rec_rules.iter()) {
                    ensure_eq!(old.ctor_name, new.ctor_name);
                    self.assert_imported_expr_matches(old.val, new.val);
                }
            }
            _ => reject!("missing imported recursor reconstructed from nested inductive"),
        }
    }
    fn restore_recursors(
        &mut self,
        st: &InductiveCheckState<'t>,
        specialized_rec_name_to_rec_name: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
    ) {
        // Check the recursors for the base inductives (NOT the specialized types)
        for old_ind_name in ind_names_no_specialized.iter().copied() {
            let rec_name = {
                let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
                self.ctx.str(old_ind_name, rec_str_ptr)
            };
            self.check_restored_recursor1(
                st,
                ind_names_no_specialized,
                specialized_rec_name_to_rec_name,
                rec_name,
            );
        }

        // Check the recursors constructed for the specialized types,
        // like `_nested.Array_1.rec` after restoring it to `Lean.Syntax.rec_1`
        for specialized_ty_rec_name in specialized_rec_name_to_rec_name.keys().copied() {
            self.check_restored_recursor1(
                st,
                ind_names_no_specialized,
                specialized_rec_name_to_rec_name,
                specialized_ty_rec_name,
            );
        }
    }
    fn check_restored_ctor1(
        &mut self,
        st: &InductiveCheckState<'t>,
        rec_name_map: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        old_ctor: &ConstructorData<'t>,
    ) {
        let new_ctor @ ConstructorData { .. } =
            self.env.get_constructor(old_ctor.info.name).unwrap();
        ensure!(old_ctor.aux_data_ck(new_ctor));
        let new_ty = self.restore_e(st, new_ctor.info.ty, rec_name_map);
        self.tc_cache.clear();
        self.assert_def_eq(old_ctor.info.ty, new_ty);
    }
    pub(super) fn restore_and_check(
        &mut self,
        st: &InductiveCheckState<'t>,
        unmodified_mutuals: &Vec<IndTyHeader<'t>>,
        ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
    ) {
        let specialized_to_unspecialized_rec_names =
            self.mk_specialized_rec_to_unspecialized_map(unmodified_mutuals);
        let base_rec_names = self.base_recursor_names(ind_names_no_specialized);
        self.assert_block_recursor_names(
            ind_names_no_specialized[0],
            base_rec_names
                .iter()
                .copied()
                .chain(specialized_to_unspecialized_rec_names.values().copied()),
        );
        for unmodified_ind_type in unmodified_mutuals {
            match (
                self.env.get_old_declar(unmodified_ind_type.name),
                self.env.get_temp_declar(unmodified_ind_type.name),
            ) {
                (Some(Declar::Inductive(old)), Some(Declar::Inductive(new))) => {
                    ensure!(old.aux_data_ck(new));
                    debug_assert!(!std::ptr::eq(old, new));
                    self.tc_cache.clear();
                    self.assert_def_eq(old.info.ty, new.info.ty);
                }
                _ => reject!("expected an inductive declaration"),
            }

            for ctor in &unmodified_ind_type.ctors {
                let ctor = match self.env.get_old_declar(ctor.name) {
                    Some(Declar::Constructor(c)) => c.clone(),
                    _ => reject!("expected a constructor declaration"),
                };
                self.check_restored_ctor1(st, &specialized_to_unspecialized_rec_names, &ctor);
            }
        }
        self.restore_recursors(
            st,
            &specialized_to_unspecialized_rec_names,
            ind_names_no_specialized,
        );
    }
}
