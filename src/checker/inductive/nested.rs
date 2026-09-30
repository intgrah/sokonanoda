// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use super::{CtorHeader, IndTyHeader, InductiveCheckState};
use crate::checker::env::{ConstructorData, InductiveData};
use crate::checker::tc::TypeChecker;
use crate::outcome::{ensure, ensure_eq};
use crate::term::expr::Expr::{App, Const, Lambda, Let, NatLit, Pi, Proj, Sort, StringLit, Var};
use crate::term::ptr::ExprPtr;

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub(super) fn specialize_nested(
        &mut self,
        t_from_file: &InductiveData<'t>,
        unmodified_tys_ctors: Vec<IndTyHeader<'t>>,
    ) -> InductiveCheckState<'t> {
        let (local_params, _instd) =
            self.get_local_params(unmodified_tys_ctors[0].ty, t_from_file.num_params);

        let mut st = InductiveCheckState::new(
            t_from_file.info.uparams,
            u16::try_from(local_params.len()).unwrap(),
            unmodified_tys_ctors,
            local_params,
        );
        // Collect the new `NestedNewType` items constructed from any actually nested inductives.
        self.specialize_nested_aux(&mut st);

        for ind in &st.all_inductives_incl_specialized {
            ensure_eq!(ind.ty.num_loose_bvars(), 0);
            for c in &ind.ctors {
                ensure_eq!(c.ty.num_loose_bvars(), 0);
            }
        }
        st
    }
    /// This function does two important things, and it sort of needs to do them together.
    ///
    /// 1. it adds any new specialized inductive types needed to handle nested inductives to the state.
    ///    For example, in the declaration for `Lean.Syntax`, adding `_nested.Array_X` to
    ///    `st.all_inductives_incl_specialized`.
    ///
    /// 2. it goes through the constructors of all the inductives, including the newly added specialized
    ///    ones, and finds instances of nested types, replacing them in with instances of the specialized types.
    ///    For example, replacing the occurrence of `Array Syntax` in the `Lean.Syntax.node` constructor
    ///    with `_nested.Array_N`.
    fn specialize_nested_aux(&mut self, st: &mut InductiveCheckState<'t>) {
        let mut i = 0usize;
        // `all_inductives_incl_specialized` begins as just the unmodified `IndTyHeader`
        // elements.
        //
        // Throughout the loop, calls to `replace_all_nested` may expand the list
        // of inductive type headers with new specialized types if this is a nested
        // inductive.
        while i < st.all_inductives_incl_specialized.len() {
            let mut new_ctors_for_i = Vec::new();
            for adjusted_ctor in &(st.all_inductives_incl_specialized[i].clone()).ctors {
                let (ctor_local_params, ctor_type_instd) =
                    self.get_local_params(adjusted_ctor.ty, st.num_params());
                let replaced_ctor_wo_params = self.replace_all_nested(ctor_type_instd, st, 0);
                let replaced_ctor_w_params =
                    self.mk_pis_dep(ctor_local_params.as_slice(), 0, replaced_ctor_wo_params);
                new_ctors_for_i.push(CtorHeader {
                    name: adjusted_ctor.name,
                    ty: replaced_ctor_w_params,
                });
            }
            // update the constructors for the inductive `i` with the replaced constructors.
            let Some(old) = st.all_inductives_incl_specialized.get_mut(i) else {
                panic!("inductive type {i} is missing")
            };
            // e.g. replace the base `Syntax.node` with the updated one that replaces `Array`.
            old.ctors = new_ctors_for_i;
            i += 1;
        }
    }
    fn is_nested_ind_app(
        &mut self,
        st: &InductiveCheckState<'t>,
        e: ExprPtr<'t>,
        offset: u16,
    ) -> Option<InductiveData<'t>> {
        if !matches!(*e, App { .. }) {
            return None;
        }
        let (_f, name, _levels, args) = e.unfold_const_apps(self.arena)?;
        // If this is an application of an inductive, like `Array A`
        let ind_ty_declar @ InductiveData { num_params, .. } = self.env.get_inductive(name)?;
        if (*num_params as usize) > args.len() {
            return None;
        }
        let params = &args[..usize::from(*num_params)];
        let is_nested = params.iter().any(|&p| {
            p.find_const(|n| {
                st.all_inductives_incl_specialized
                    .iter()
                    .any(|new_ty| new_ty.name == n)
            })
        });
        if !is_nested {
            return None;
        }
        ensure!(
            !params.iter().any(|&p| p.has_loose_bvar_below(offset)),
            "a nested type may only be applied to the block's parameters"
        );
        Some(ind_ty_declar.clone())
    }
    /// *THIS METHOD MAY PUSH NEW SPECIALIZED INDUCTIVES TO THE STATE*
    ///
    /// `e` is a constructor or part of some constructor for an inductive or specialized inductive
    /// in this block.
    ///
    ///
    /// if `e` is a nested occurrence/application, like the `Array Syntax` argument to
    /// the `Lean.Syntax.node` constructor, replace `Array Syntax` with `_nested.Array_X`.
    fn replace_if_nested(
        &mut self,
        e: ExprPtr<'t>,
        st: &mut InductiveCheckState<'t>,
        offset: u16,
    ) -> Option<ExprPtr<'t>> {
        // Using the `Lean.Syntax.node` constructor as an example, if `e` is the application of
        // `Array Lean.Syntax`, this variable will be the base declaration for `Array`.
        let nested_container_ty = self.is_nested_ind_app(st, e, offset)?;
        // Get the `Array` from `Array Syntax`
        let (f, i_name, i_levels, args) = e.unfold_const_apps(self.arena).unwrap();
        assert!(nested_container_ty.num_params as usize <= args.len());
        // Reapply the portion of the unfolded applications that is the parameters.
        let i_as = self.ctx.foldl_apps(
            f,
            args.iter()
                .copied()
                .take(nested_container_ty.num_params as usize),
        );
        let i_params = self.ctx.lower(i_as, 0, offset);
        let outgoing_param_vars = self.param_vars(st, offset);

        if let Some((aux_i_name, _)) = st
            .nested_to_unspecialized_ty
            .iter()
            .find(|(_name, expr)| **expr == i_params)
        {
            let f = self.ctx.mk_const(*aux_i_name, st.uparams);
            let f = self.ctx.foldl_apps(f, outgoing_param_vars.iter().copied());
            let f = self.ctx.foldl_apps(
                f,
                (args[(nested_container_ty.num_params as usize)..args.len()])
                    .iter()
                    .copied(),
            );
            Some(f)
        } else {
            let mut result: Option<ExprPtr> = None;
            // `Array`, `List`, and any mutuals in the appropriate block etc.
            for nested_container_name in nested_container_ty.all_ind_names.iter().copied() {
                // The inductive declaration for the container type, like `Array`
                let InductiveData {
                    info: container_ty_info,
                    all_ctor_names: all_nested_container_ctor_names,
                    ..
                } = self.env.get_inductive(nested_container_name)?;
                // `i_levels` is the set of uparams we actually found in the declaration we're checking,
                // so the set of uparams in `Lean.Syntax`, as opposed to the uparam declars for `Array`
                let js = {
                    let base_const = self.ctx.mk_const(nested_container_name, i_levels);
                    self.ctx.foldl_apps(
                        base_const,
                        (args[0..nested_container_ty.num_params as usize])
                            .iter()
                            .copied(),
                    )
                };

                // Example: From `Array`, make `_nested.Array_1`
                let aux_nested_container_name = {
                    let nested_pfx = self.ctx.str1("_nested");
                    let base = self.ctx.concat_name(nested_pfx, nested_container_name);
                    self.mk_unique_name(base, st)
                };
                // Replace the telescope on the auxiliary declaration to match the declaration
                // we're currently checking. Can also add parameters as needed.
                let nested_container_aux_type = {
                    let base = self.ctx.subst_expr_levels(
                        container_ty_info.ty,
                        container_ty_info.uparams,
                        i_levels,
                    );
                    let instd = self.ctx.inst_forall_params(
                        base,
                        nested_container_ty.num_params as usize,
                        args.as_slice(),
                    );
                    let instd = self.ctx.lower(instd, 0, offset);
                    let params = st.local_params.clone();
                    self.mk_pis_dep(params.as_slice(), 0, instd)
                };
                let jsprime = self.ctx.lower(js, 0, offset);
                st.nested_to_unspecialized_ty
                    .insert(aux_nested_container_name, jsprime);
                if nested_container_name == i_name {
                    let f = self.ctx.mk_const(aux_nested_container_name, st.uparams);
                    let f = self.ctx.foldl_apps(f, outgoing_param_vars.iter().copied());
                    let args = &args[nested_container_ty.num_params as usize..args.len()];
                    let f = self.ctx.foldl_apps(f, args.iter().copied());
                    result = Some(f);
                }
                let mut auxj_ctors = Vec::<CtorHeader>::new();
                for j_ctor_name in all_nested_container_ctor_names.iter().copied() {
                    let ConstructorData {
                        info: j_ctor_info, ..
                    } = self.env.get_constructor(j_ctor_name)?;
                    // Replace `Array.mk` with `_nested.Array_2.mk`
                    let auxj_ctor_name = self.ctx.replace_pfx(
                        j_ctor_name,
                        nested_container_name,
                        aux_nested_container_name,
                    );
                    let auxj_ctor_type =
                        self.ctx
                            .subst_expr_levels(j_ctor_info.ty, j_ctor_info.uparams, i_levels);
                    let auxj_ctor_type = self.ctx.inst_forall_params(
                        auxj_ctor_type,
                        nested_container_ty.num_params as usize,
                        args.as_slice(),
                    );
                    let auxj_ctor_type = self.ctx.lower(auxj_ctor_type, 0, offset);
                    let params = st.local_params.clone();
                    let auxj_ctor_type = self.mk_pis_dep(params.as_slice(), 0, auxj_ctor_type);
                    auxj_ctors.push(CtorHeader {
                        name: auxj_ctor_name,
                        ty: auxj_ctor_type,
                    });
                }
                st.all_inductives_incl_specialized.push(IndTyHeader {
                    name: aux_nested_container_name,
                    ty: nested_container_aux_type,
                    ctors: auxj_ctors,
                });
            }
            result
        }
    }
    fn replace_all_nested(
        &mut self,
        e: ExprPtr<'t>,
        st: &mut InductiveCheckState<'t>,
        offset: u16,
    ) -> ExprPtr<'t> {
        // Try to replace locally before traversing into the lower parts.
        if let Some(eprime) = self.replace_if_nested(e, st, offset) {
            eprime
        } else {
            match *e {
                Var { .. } | Sort { .. } | Const { .. } | NatLit { .. } | StringLit { .. } => e,
                Pi {
                    binder_type, body, ..
                } => {
                    let binder_type = self.replace_all_nested(binder_type, st, offset);
                    let body = self.replace_all_nested(body, st, offset + 1);
                    self.ctx.mk_pi(binder_type, body)
                }
                Lambda {
                    binder_type, body, ..
                } => {
                    let binder_type = self.replace_all_nested(binder_type, st, offset);
                    let body = self.replace_all_nested(body, st, offset + 1);
                    self.ctx.mk_lambda(binder_type, body)
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
                    let binder_type = self.replace_all_nested(binder_type, st, offset);
                    let val = self.replace_all_nested(val, st, offset);
                    let body = self.replace_all_nested(body, st, offset + 1);
                    self.ctx.mk_let(binder_type, val, body, nondep)
                }
                App { fun, arg, .. } => {
                    let fun = self.replace_all_nested(fun, st, offset);
                    let arg = self.replace_all_nested(arg, st, offset);
                    self.ctx.mk_app(fun, arg)
                }
                Proj {
                    ty_name,
                    idx,
                    structure,
                    ..
                } => {
                    let structure = self.replace_all_nested(structure, st, offset);
                    self.ctx.mk_proj(ty_name, idx, structure)
                }
            }
        }
    }
}
