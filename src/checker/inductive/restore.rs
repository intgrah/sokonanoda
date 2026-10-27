// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use super::{IndTyHeader, InductiveCheckState};
use crate::checker::env::{
    ConstructorData, Declar, DeclarInfo, InductiveData, RecRule, RecursorData,
};
use crate::checker::tc::TypeChecker;
use crate::checker::value::Value;
use crate::outcome::reject;
use crate::term::expr::Expr::{Const, Pi};
use crate::term::hash::FxIndexMap;
use crate::term::id::{ExprId, NameId};
use std::sync::Arc;

impl<'x, 't: 'x> TypeChecker<'x, 't> {
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
        base_mutuals: &[IndTyHeader],
    ) -> FxIndexMap<NameId, NameId> {
        // The unmodified name of the "main" type being checked, e.g. `Lean.Syntax`
        let main_ind_ty_name = base_mutuals.first().map(|zth| zth.name).unwrap();
        let mut specialized_rec_names_to_unspecialized_rec_names =
            crate::term::hash::new_fx_index_map();
        let rec_str = self.ctx.alloc_string("rec");

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
        st: &InductiveCheckState,
        c: NameId,
    ) -> Option<(ExprId, NameId)> {
        // `inductive_name`
        let ConstructorData { inductive_name, .. } = self.env.get_constructor(c)?;
        let unspecialized_ty = st.nested_to_unspecialized_ty.get(inductive_name).copied()?;
        Some((unspecialized_ty, *inductive_name))
    }
    /// If `c` is `_nested_Array_1.mk`, return just `Array.mk`,
    ///
    /// This is only used in restoring recursor rules, since those hold the constructor name.
    fn restore_ctor_name(&mut self, st: &InductiveCheckState, ctor_name: NameId) -> NameId {
        // from `_nested_Array_1.mk`, retrieve `(Array Lean.Syntax, _nested.Array_1)`
        let (unspecialized_ty, base_ind_name) = self.get_nested_if_aux_ctor(st, ctor_name).unwrap();
        // Now get just `Const(Array, [])`
        let unspecialized_f = self.ctx.unfold_apps_fun(unspecialized_ty);
        // Get just the name for `Array`
        let (unspecialized_ty_name, ..) = self.ctx.try_const_info(unspecialized_f).unwrap();
        // Replace ctor_name[specialized_name |-> unspecialized_name]
        // e.g. `_nested.Array_1.mk |-> Array.mk`
        self.ctx
            .replace_pfx(ctor_name, base_ind_name, unspecialized_ty_name)
    }
    fn restore_replace(
        &mut self,
        e: ExprId,
        num_params: usize,
        depth: u16,
        st: &InductiveCheckState,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NameId, NameId>,
    ) -> ExprId {
        match self.replace_f(
            e,
            num_params,
            depth,
            st,
            specialized_rec_names_to_unspecialized_rec_names,
        ) {
            Some(out) => out,
            None => {
                let expr = self.ctx.ex(e).map_children(|child, binders| {
                    self.restore_replace(
                        child,
                        num_params,
                        depth + binders,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    )
                });
                self.ctx.rebuild_expr(e, expr)
            }
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
        e: ExprId,
        num_params: usize,
        depth: u16,
        st: &InductiveCheckState,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NameId, NameId>,
    ) -> Option<ExprId> {
        // If it's a recursor application, update the recursor.
        // e.g.
        // replacing(1) const _nested.Lean.PersistentArrayNode_2.rec with Lean.Elab.InfoTree.rec_2
        // replacing(1) const _nested.List_6.rec with Lean.Elab.InfoTree.rec_6
        if let Const { name, levels } = self.ctx.ex(e) {
            // If e was `Const(_nested.Array_1.rec)`, return `Const(Lean.Syntax.rec_1)`
            if let Some(rec_name) = specialized_rec_names_to_unspecialized_rec_names.get(&name) {
                return Some(self.ctx.mk_const(*rec_name, levels));
            }
        }
        let (_, c_name, _, e_args) = self.ctx.unfold_const_apps(e)?;
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
        let (nested_f, i_args) = self.ctx.unfold_apps(nested_inst);
        // Replace one of the nested constructor applications with a regular ctor application.
        //
        // replacing(3) c := _nested.Array_3.mk, auxI_name := _nested.Array_3, I_c := Array, c' := Array.mk.{0}
        // replacing(3) c := _nested.List_4.nil, auxI_name := _nested.List_4, I_c := List, c' := List.nil.{0}
        match self.ctx.ex(nested_f) {
            Const {
                name: i_name,
                levels,
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
        st: &InductiveCheckState,
        e: ExprId,
        nested_rec_name_to_rec_name: &FxIndexMap<NameId, NameId>,
    ) -> ExprId {
        let is_pi = matches!(self.ctx.ex(e), Pi { .. });
        let num_params = st.local_params.len();
        let mut cur = self.value_of(e);
        let mut binders: Vec<ExprId> = Vec::with_capacity(num_params);
        for level in 0..num_params {
            let depth = u32::try_from(level).expect("parameter count exceeds u32");
            let f = cur;
            let dom = match self.val(f) {
                Value::Pi { domain, .. } => domain,
                // Also match on Lambda for restoring recursor rules.
                Value::Lam { .. } => self.lam_domain(depth, f),
                _ => reject!("malformed recursor"),
            };
            let dom_e = self.quote(depth, dom);
            let fresh = self.mk_bvar_hc(depth, dom);
            cur = match self.val(f) {
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
        st: &InductiveCheckState,
        // The list of names in the mutual block, NOT including
        // the temporary nested declarations.
        all_ind_names_no_specialized: &Arc<[NameId]>,
        // This map holds the specialized nested elements' recursor names;
        // e.g. `_nested.Array_1.rec |-> Lean.Syntax.rec_1`,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NameId, NameId>,
        // `rec_name` This can be either an old/base inductive rec name, or a fresh/specialized name
        // Either `Syntax.rec`, or `_nested.Array_N.rec`
        rec_name: NameId,
    ) -> RecursorData {
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
        let rules: Arc<[RecRule]> = new_env_rec
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
    pub(super) fn restore_recursors(
        &mut self,
        st: &InductiveCheckState,
        unmodified: &[IndTyHeader],
        ind_names: &Arc<[NameId]>,
    ) -> Vec<Declar> {
        let names = self.mk_specialized_rec_to_unspecialized_map(unmodified);
        let rec = self.ctx.alloc_string("rec");
        let base: Vec<_> = ind_names
            .iter()
            .map(|name| self.ctx.str(*name, rec))
            .collect();
        base.into_iter()
            .chain(names.keys().copied())
            .map(|name| Declar::Recursor(self.restore_recursor1(st, ind_names, &names, name)))
            .collect()
    }
}
