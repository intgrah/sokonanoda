// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::context::{ExportFile, TcCtx};
use crate::checker::env::{ConstructorData, Declar, DeclarInfo, DeclarMap, InductiveData};
use crate::checker::tc::TypeChecker;
use crate::checker::value::Value;
use crate::outcome::reject;
use crate::term::hash::FxIndexMap;
use crate::term::id::{ExprId, LevelId, LevelsId, NameId};
use std::sync::Arc;

mod nested;
pub(crate) mod persist;
mod positivity;
mod recursor;
mod restore;
mod spec;

#[cfg(test)]
mod tests;

use positivity::check_uniform_inductive_occurrences;

impl ExportFile {
    pub(crate) fn check_inductive_declar<'t>(
        &'t self,
        ctx: &mut TcCtx<'t>,
        cache: &mut crate::checker::cache::TcCache,
        ind: &InductiveData,
    ) -> Vec<Declar> {
        let &(start, _) = self
            .mutual_block_sizes
            .get(&ind.info.name)
            .expect("missing inductive block boundaries");
        let env_limit = crate::checker::env::EnvLimit::ByIndex(start);
        {
            let unmodified_tys_ctors = ctx.with_tc(env_limit, cache, |tc| {
                for name in ind.all_ind_names.iter() {
                    let declar = &self.declars[name];
                    tc.tc_cache.clear();
                    tc.ctx.next_declaration();
                    tc.declar_info = Some(*declar.info());
                    tc.check_declar_info_v(declar);
                }
                tc.collect_unmodified_mutuals(ind)
            });

            for header in &unmodified_tys_ctors {
                for ctor in &header.ctors {
                    check_uniform_inductive_occurrences(
                        ctx,
                        ctor.ty,
                        &ind.all_ind_names,
                        ind.info.uparams,
                        ind.num_params,
                    );
                }
            }

            let type_specs: DeclarMap = ind
                .all_ind_names
                .iter()
                .map(|&name| {
                    (
                        name,
                        Declar::Axiom {
                            info: *self.declars[&name].info(),
                        },
                    )
                })
                .collect();
            ctx.with_tc_and_env_ext(&type_specs, env_limit, cache, |tc| {
                for header in &unmodified_tys_ctors {
                    for ctor in &header.ctors {
                        let declar = &self.declars[&ctor.name];
                        tc.tc_cache.clear();
                        tc.ctx.next_declaration();
                        tc.declar_info = Some(*declar.info());
                        tc.check_declar_info_v(declar);
                    }
                }
            });

            // Initialize the big chunk of state used throughout the process of checking
            // this inductive declaration.
            let mut st = ctx.with_tc(env_limit, cache, |tc| {
                tc.specialize_nested(ind, unmodified_tys_ctors.clone())
            });

            // Check the (potentially modified) inductive specs against the base environment.
            ctx.with_tc(env_limit, cache, |tc| {
                tc.check_inductive_specs(&mut st);
            });

            // The first temporary environment extension, containing any specialized
            // types to deal with nested inductives.
            let ind_ty_ext1 = st.ind_tys_env_ext();

            // Check the constructors against the environment with the base extension.
            ctx.with_tc_and_env_ext(&ind_ty_ext1, env_limit, cache, |tc| {
                for ind in &st.all_inductives_incl_specialized {
                    for ctor in &ind.ctors {
                        tc.check_ctor(&st, ind.name, ctor.ty);
                    }
                }
            });

            // The second temporary environment extension, which also includes the constructors.
            let ctor_extension = st.ctors_env_ext(ctx, ind_ty_ext1);

            // The constructed recursors and rec rules
            let recursors = ctx.with_tc_and_env_ext(&ctor_extension, env_limit, cache, |tc| {
                tc.mk_elim_level(&mut st);
                st.init_k_target(&tc.ctx);
                tc.mk_majors(&mut st);
                tc.mk_motives(&mut st);
                tc.mk_minors(&mut st);
                tc.mk_recursors(&st)
            });

            // The last temporary environment extension, which also includes the recursors.
            let recursor_extension = {
                let mut out = ctor_extension;
                for r in recursors.clone() {
                    out.insert(r.info().name, r);
                }
                out
            };

            ctx.with_tc_and_env_ext(&recursor_extension, env_limit, cache, |tc| {
                tc.check_generated_recursors(&st, &recursors);
                let rec_names: Vec<_> = recursors.iter().map(|rec| rec.info().name).collect();
                let is_recursive = recursors.iter().any(|rec| {
                    let Declar::Recursor(rec) = rec else {
                        unreachable!()
                    };
                    rec.rec_rules.iter().any(|rule| {
                        tc.ctx
                            .find_const(rule.val, |name| rec_names.contains(&name))
                    })
                });
                let mut derived = tc.mk_declars(&st, &unmodified_tys_ctors, is_recursive);
                if st.is_nested() {
                    derived.extend(tc.restore_recursors(
                        &st,
                        &unmodified_tys_ctors,
                        &ind.all_ind_names,
                    ));
                } else {
                    derived.extend(recursors);
                }
                derived
            })
        }
    }
}

pub(crate) struct InductiveCheckState {
    /// Maps the specialized type's fresh name to its "actual"/unspecialized type,
    /// where the type uses bound variables instead of free variables.
    ///
    /// Example contents for `Sexpr`:\
    /// ```ignore
    /// (_nested.List_1, (List.[u] (Sexpr.[u] $0)))
    /// ```
    ///
    /// Example contents for `Lean.Syntax`:\
    /// ```ignore
    /// (_nested.Array_1, (Array.[0] Lean.Syntax.[]))
    /// (_nested.List_2, (List.[0] Lean.Syntax.[]))
    /// ```
    nested_to_unspecialized_ty: FxIndexMap<NameId, ExprId>,
    uparams: LevelsId,
    // NOTE: All of the inductives in a mutual block have to be declared with the same
    // number of parameters, and after specialization, the mutuals that are specialized
    // nested types will also have the same number of params as the block. This means that
    // if a nested container type has fewer params than the block, the block will gain more
    // parameters.
    num_params: u16,
    /// This is all of the inductive types in the current mutual block, PLUS any temoprary extensions
    /// generated by nested inductives.
    all_inductives_incl_specialized: Vec<IndTyHeader>,
    /// Used for generating fresh names when specializing nested inductives.
    /// Needs to be incrementing because you may have more than one specialized
    /// version of a given container type.
    next_ngen_idx: u64,
    local_params: Vec<ExprId>,
    local_indices: Vec<Vec<ExprId>>,
    block_codom: Option<LevelId>,
    is_zero: Option<bool>,
    is_nonzero: Option<bool>,
    ind_consts: Vec<ExprId>,
    rec_uparams: Option<LevelsId>,
    elim_level: Option<LevelId>,
    k_target: Option<bool>,
    majors: Vec<ExprId>,
    motives: Vec<ExprId>,
    minors: Vec<Vec<ExprId>>,
}

impl InductiveCheckState {
    /// To be a target for k-like reduction, a type cannot be mutual or nested, must be an inductive
    /// prop, must have only one constructor, and the constructor can take only the type's parameters
    /// as arguments.
    fn init_k_target(&mut self, ctx: &TcCtx<'_>) {
        let is_k_target = self.is_zero.unwrap()
            && self.all_inductives_incl_specialized.len() == 1
            && match self.all_inductives_incl_specialized[0].ctors.as_slice() {
                [only_ctor] => {
                    ctx.pi_telescope_size(only_ctor.ty) as usize == self.local_params.len()
                }
                _ => false,
            };
        self.k_target = Some(is_k_target);
    }

    /// Extend the current environment with new constructors, including modifications
    /// to accommodate any temporary declarations that come from nested inductives.
    fn ctors_env_ext(&self, ctx: &TcCtx<'_>, mut env_ext: DeclarMap) -> DeclarMap {
        // This will be different from the export file's list if this is a nested.
        for inductive in &self.all_inductives_incl_specialized {
            for (idx, ctor) in inductive.ctors.iter().copied().enumerate() {
                let info = DeclarInfo {
                    name: ctor.name,
                    ty: ctor.ty,
                    uparams: self.uparams,
                };
                let num_params = u16::try_from(self.local_params.len()).unwrap();
                let num_fields = ctx.pi_telescope_size(ctor.ty) - num_params;
                let d = Declar::Constructor(ConstructorData {
                    info,
                    inductive_name: inductive.name,
                    ctor_idx: u16::try_from(idx).unwrap(),
                    num_params,
                    num_fields,
                });
                env_ext.insert(ctor.name, d);
            }
        }
        env_ext
    }

    /// Extend the current environment with the inductive specifications,
    /// including modifications to accommodate any temporary declarations
    /// that come from nested inductives.
    fn ind_tys_env_ext(&self) -> DeclarMap {
        // This will be different from the export file's list if this is a nested.
        let is_nested = !self.nested_to_unspecialized_ty.is_empty();
        let all_ind_names: Arc<[NameId]> = self
            .all_inductives_incl_specialized
            .iter()
            .map(|x| x.name)
            .collect();
        let mut env_extension = crate::term::hash::new_fx_index_map();
        for (idx, inductive) in self.all_inductives_incl_specialized.iter().enumerate() {
            let t = Declar::Inductive(InductiveData {
                info: DeclarInfo {
                    name: inductive.name,
                    ty: inductive.ty,
                    uparams: self.uparams,
                },
                is_nested,
                is_recursive: false,
                num_params: u16::try_from(self.local_params.len()).unwrap(),
                num_indices: u16::try_from((self.local_indices[idx]).len()).unwrap(),
                all_ind_names: all_ind_names.clone(),
                all_ctor_names: inductive.ctors.iter().map(|x| x.name).collect(),
            });
            env_extension.insert(inductive.name, t);
        }
        env_extension
    }

    fn new(
        info_uparams: LevelsId,
        num_params: u16,
        new_tys: Vec<IndTyHeader>,
        local_params: Vec<ExprId>,
    ) -> Self {
        Self {
            nested_to_unspecialized_ty: crate::term::hash::new_fx_index_map(),
            uparams: info_uparams,
            num_params,
            all_inductives_incl_specialized: new_tys,
            next_ngen_idx: 1u64,
            local_params,
            local_indices: Vec::new(),
            block_codom: None,
            is_zero: None,
            is_nonzero: None,
            ind_consts: Vec::new(),
            rec_uparams: None,
            elim_level: None,
            k_target: None,
            majors: Vec::new(),
            motives: Vec::new(),
            minors: Vec::new(),
        }
    }
    fn is_nested(&self) -> bool {
        !self.nested_to_unspecialized_ty.is_empty()
    }

    fn num_params(&self) -> u16 {
        u16::try_from(self.local_params.len()).expect("parameter count exceeds u16")
    }

    fn num_motives(&self) -> u16 {
        u16::try_from(self.motives.len()).expect("motive count exceeds u16")
    }

    fn minor_base(&self) -> u16 {
        self.num_params() + self.num_motives()
    }

    fn flat_minors(&self) -> Vec<ExprId> {
        self.minors.iter().flat_map(|v| v.iter().copied()).collect()
    }
}

#[derive(Debug, Clone)]
struct IndTyHeader {
    name: NameId,
    ty: ExprId,
    ctors: Vec<CtorHeader>,
}

#[derive(Debug, Clone, Copy)]
struct CtorHeader {
    name: NameId,
    ty: ExprId,
}

impl<'x, 't: 'x> TypeChecker<'x, 't> {
    fn mk_declars(
        &self,
        st: &InductiveCheckState,
        headers: &[IndTyHeader],
        is_recursive: bool,
    ) -> Vec<Declar> {
        let all_ind_names: Arc<[_]> = headers.iter().map(|header| header.name).collect();
        let mut out = Vec::new();
        for (idx, header) in headers.iter().enumerate() {
            let info = DeclarInfo {
                name: header.name,
                uparams: st.uparams,
                ty: header.ty,
            };
            let num_params = st.num_params();
            let num_indices = u16::try_from(st.local_indices[idx].len()).unwrap();
            out.push(Declar::Inductive(InductiveData {
                info,
                is_recursive,
                is_nested: st.is_nested(),
                num_params,
                num_indices,
                all_ind_names: all_ind_names.clone(),
                all_ctor_names: header.ctors.iter().map(|ctor| ctor.name).collect(),
            }));
            for (idx, ctor) in header.ctors.iter().enumerate() {
                let num_fields = self.env.get_constructor(ctor.name).unwrap().num_fields;
                out.push(Declar::Constructor(ConstructorData {
                    info: DeclarInfo {
                        name: ctor.name,
                        ty: ctor.ty,
                        uparams: info.uparams,
                    },
                    inductive_name: header.name,
                    ctor_idx: u16::try_from(idx).expect("too many constructors"),
                    num_params,
                    num_fields,
                }));
            }
        }
        out
    }

    fn get_local_params(&mut self, e: ExprId, num_params: u16) -> (Vec<ExprId>, ExprId) {
        let mut depth = 0u32;
        let mut params = Vec::with_capacity(num_params as usize);
        let mut cur = self.value_of(e);
        for _ in 0..num_params {
            let Some(Value::Pi { domain, body, .. }) = self.force_pi(depth, cur) else {
                reject!("exhausted telescope early")
            };
            let binder_type = self.quote(depth, domain);
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
            params.push(binder_type);
        }
        let rest = self.quote(depth, cur);
        (params, rest)
    }

    fn param_var(&mut self, st: &InductiveCheckState, offset: u16, i: u16) -> ExprId {
        self.ctx.mk_var(offset + st.num_params() - 1 - i)
    }

    fn param_vars(&mut self, st: &InductiveCheckState, offset: u16) -> Vec<ExprId> {
        (0..st.num_params())
            .map(|i| self.param_var(st, offset, i))
            .collect()
    }

    fn mk_pis_dep(&mut self, binders: &[ExprId], gap: u16, mut body: ExprId) -> ExprId {
        for (i, ty) in binders.iter().copied().enumerate().rev() {
            let ty = self
                .ctx
                .lift(ty, u16::try_from(i).expect("telescope exceeds u16"), gap);
            body = self.ctx.mk_pi(ty, body);
        }
        body
    }

    fn mk_pis_flat(&mut self, binders: &[ExprId], mut body: ExprId) -> ExprId {
        for (i, ty) in binders.iter().copied().enumerate().rev() {
            let ty = self
                .ctx
                .lift(ty, 0, u16::try_from(i).expect("telescope exceeds u16"));
            body = self.ctx.mk_pi(ty, body);
        }
        body
    }

    fn mk_lambdas_dep(&mut self, binders: &[ExprId], gap: u16, mut body: ExprId) -> ExprId {
        for (i, ty) in binders.iter().copied().enumerate().rev() {
            let ty = self
                .ctx
                .lift(ty, u16::try_from(i).expect("telescope exceeds u16"), gap);
            body = self.ctx.mk_lambda(ty, body);
        }
        body
    }

    fn mk_lambdas_flat(&mut self, binders: &[ExprId], mut body: ExprId) -> ExprId {
        for (i, ty) in binders.iter().copied().enumerate().rev() {
            let ty = self
                .ctx
                .lift(ty, 0, u16::try_from(i).expect("telescope exceeds u16"));
            body = self.ctx.mk_lambda(ty, body);
        }
        body
    }

    fn header_of_ty(&self, t: &InductiveData) -> IndTyHeader {
        fn header_of_ctor(t: &ConstructorData) -> CtorHeader {
            CtorHeader {
                name: t.info.name,
                ty: t.info.ty,
            }
        }
        let ctors = t
            .all_ctor_names
            .iter()
            .map(|ctor_name| {
                header_of_ctor(match &self.ctx.export_file.declars[ctor_name] {
                    Declar::Constructor(ctor) => ctor,
                    _ => unreachable!(),
                })
            })
            .collect();
        IndTyHeader {
            name: t.info.name,
            ty: t.info.ty,
            ctors,
        }
    }

    /// For some exported inductive declaration `T` that has a list of mutual names
    /// `[T, U, .., Z]`, return the `IndTyHeader` elements for `[T, U, .., Z]`, without
    /// any specializations/modifications.
    fn collect_unmodified_mutuals(&self, t_from_file: &InductiveData) -> Vec<IndTyHeader> {
        // Get all of the mutual inductives, but don't re-insert the base type.
        t_from_file
            .all_ind_names
            .iter()
            .map(|n| {
                self.header_of_ty(match &self.ctx.export_file.declars[n] {
                    Declar::Inductive(ind) => ind,
                    _ => unreachable!(),
                })
            })
            .collect()
    }

    fn mk_unique_name(&mut self, n: NameId, st: &mut InductiveCheckState) -> NameId {
        for idx in st.next_ngen_idx..u64::MAX {
            let tester = self.ctx.append_index_after(n, idx);
            if tester.is_local() {
                st.next_ngen_idx = idx + 1;
                return tester;
            }
        }
        panic!("Unable to generate unique name, u64 exhausted")
    }

    // This is only ONE of the binders from the constructor's telescope,
    // AFTER the block params have been removed. These are the "proper"
    // constructor arguments.
    //
    // When we match here on Pi { n, t, s, b }, `t` is the left hand side
    // of a function argument to an inductive constructor.
    // We need to search `t` to prevent non-positive occurrences; the following
    // would be prohibited:
    //
    //```ignore
    // inductive Foo
    // | mk (f : Foo → Nat) : Foo
    //```
    //
    // Read about issues with non-positive occurrences here:
    // https://counterexamples.org/strict-positivity.html?highlight=posi#positivity-strict-and-otherwise

    // For an expression `E` and a list
    // of names `NS`, recursively search through `E` for a `Const { name, levels }`
    // `C`, whose name is ANY of the names in `NS`. If such a `C` exists,
    // return true, else return false.
    //
    // This is used in the formation of inductive types, to determine whether
    // a type is recursive, reflexive, contains only positive occurrences, and
    // has only valid applications.

    // Test large elimination for an inductive that we know is...
    // 1. An inductive predicate (is in `Prop`)
    // 1. Not a mutual inductive
    // 3. Has exactly one constructor.
    //
    // This kind of inductive prop is okay for large elimination IFF every
    // non-prop ctor arg is a param or index of the inductive type.
    //
    // Example: This inductive prop is okay for large elimination, because `n` is an index.
    //```
    // inductive MyTypeLarge (A : Type) : Nat → Prop
    // | mk (n : Nat) : MyTypeLarge A n
    // ```
    //
    // This type is not okay for large elimination, because `m` is neither a parameter nor an index.
    //```
    // inductive MyTypeSmall (A : Type) : Nat → Prop
    // | mk (m : Nat) (n : Nat) : MyTypeSmall A n
    //```

    // Assert that the inductive types being added to the extension which
    // are also in the export file are definitionally equal.
}
