// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::context::{ExportFile, TcCtx};
use crate::checker::env::{ConstructorData, Declar, DeclarInfo, DeclarMap, InductiveData};
use crate::checker::tc::TypeChecker;
use crate::checker::value::Value;
use crate::outcome::{ensure, ensure_eq, reject};
use crate::term::expr::Expr::Pi;
use crate::term::hash::{FxHashSet, FxIndexMap};
use crate::term::ptr::{ExprPtr, LevelPtr, LevelsPtr, NamePtr};
use std::sync::Arc;

mod nested;
mod positivity;
mod recursor;
mod restore;
mod spec;

use positivity::check_uniform_inductive_occurrences;

impl<'t, 'p: 't> ExportFile<'p> {
    pub(crate) fn check_inductive_declar(
        &'t self,
        ctx: &mut TcCtx<'t, 'p>,
        cache: &mut crate::checker::cache::TcCache<'t, 't>,
        arena: &'t bumpalo::Bump,
        d: &Declar<'t>,
    ) {
        let (ind, env_limit) = match d {
            Declar::Inductive(ind) => {
                let &(start, size) = self
                    .mutual_block_sizes
                    .get(&ind.info.name)
                    .expect("missing inductive block boundaries");
                let mut physical_ind_names = Vec::new();
                let mut physical_ctor_types = Vec::new();
                let mut physical_inductive_types_and_ctors = Vec::new();
                for idx in start..start + size {
                    let (_, declar) = self
                        .declars
                        .get_index(idx)
                        .expect("inductive block boundary exceeds environment");
                    match declar {
                        Declar::Inductive(inductive) => {
                            physical_ind_names.push(inductive.info.name);
                            physical_inductive_types_and_ctors.push(inductive.info.ty);
                        }
                        Declar::Constructor(constructor) => {
                            physical_ctor_types.push(constructor.info.ty);
                            physical_inductive_types_and_ctors.push(constructor.info.ty);
                        }
                        _ => {}
                    }
                }
                ensure!(
                    !physical_ind_names.is_empty(),
                    "inductive block contains no inductive types"
                );

                for ty in physical_ctor_types.iter().copied() {
                    check_uniform_inductive_occurrences(
                        ty,
                        physical_ind_names.as_slice(),
                        ind.info.uparams,
                        ind.num_params,
                    );
                }
                let nested = ctx.str1("_nested");
                for ty in physical_inductive_types_and_ctors.iter().copied() {
                    ensure!(
                        !ctx.has_nested_name(ty, nested),
                        "reserved _nested name in inductive block"
                    );
                }
                let is_recursive = 'found: {
                    for mut ctor_ty in physical_ctor_types.iter().copied() {
                        while let Pi {
                            binder_type, body, ..
                        } = *ctor_ty
                        {
                            if binder_type.find_const(|name| physical_ind_names.contains(&name)) {
                                break 'found true;
                            }
                            ctor_ty = body;
                        }
                    }
                    false
                };
                ensure_eq!(ind.is_recursive, is_recursive);
                (ind, crate::checker::env::EnvLimit::ByIndex(start + size))
            }
            _ => reject!("expected inductive"),
        };
        {
            // The **unmodified** types and constructors for all of the types in this mutual block.
            let unmodified_tys_ctors = ctx.with_tc(env_limit, arena, cache, |tc| {
                tc.check_declar_info_v(d);
                tc.collect_unmodified_mutuals(ind)
            });

            // Initialize the big chunk of state used throughout the process of checking
            // this inductive declaration.
            let mut st = ctx.with_tc(env_limit, arena, cache, |tc| {
                tc.specialize_nested(ind, unmodified_tys_ctors.clone())
            });

            // Check the (potentially modified) inductive specs against the base environment.
            ctx.with_tc(env_limit, arena, cache, |tc| {
                tc.check_inductive_specs(&mut st);
            });

            // The first temporary environment extension, containing any specialized
            // types to deal with nested inductives.
            let ind_ty_ext1 = st.ind_tys_env_ext();

            // Check the constructors against the environment with the base extension.
            ctx.with_tc_and_env_ext(&ind_ty_ext1, env_limit, arena, cache, |tc| {
                for ind in &st.all_inductives_incl_specialized {
                    for ctor in &ind.ctors {
                        tc.check_ctor(&st, ind.name, ctor.ty);
                    }
                }
            });

            // The second temporary environment extension, which also includes the constructors.
            let ctor_extension = st.ctors_env_ext(ind_ty_ext1);

            // The constructed recursors and rec rules
            let recursors =
                ctx.with_tc_and_env_ext(&ctor_extension, env_limit, arena, cache, |tc| {
                    tc.mk_elim_level(&mut st);
                    st.init_k_target();
                    tc.check_declared_metadata(&st, &unmodified_tys_ctors);
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

            ctx.with_tc_and_env_ext(&recursor_extension, env_limit, arena, cache, |tc| {
                tc.check_generated_recursors(&st, &recursors);
                if st.is_nested() {
                    tc.restore_and_check(&st, &unmodified_tys_ctors, &ind.all_ind_names);
                } else {
                    tc.assert_block_recursor_names(
                        ind.info.name,
                        recursors.iter().map(|recursor| recursor.info().name),
                    );
                    // Do the definitional equality assertions of new/old here.
                    tc.assert_nonnested_tys_def_eq(ind, &st);
                    tc.assert_nonnested_ctors_def_eq(&st);
                    tc.assert_nonnested_recursors_def_eq(&st, &recursors);
                }
            });
        }
    }
}

pub(crate) struct InductiveCheckState<'a> {
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
    nested_to_unspecialized_ty: FxIndexMap<NamePtr<'a>, ExprPtr<'a>>,
    uparams: LevelsPtr<'a>,
    // NOTE: All of the inductives in a mutual block have to be declared with the same
    // number of parameters, and after specialization, the mutuals that are specialized
    // nested types will also have the same number of params as the block. This means that
    // if a nested container type has fewer params than the block, the block will gain more
    // parameters.
    num_params: u16,
    /// This is all of the inductive types in the current mutual block, PLUS any temoprary extensions
    /// generated by nested inductives.
    all_inductives_incl_specialized: Vec<IndTyHeader<'a>>,
    /// Used for generating fresh names when specializing nested inductives.
    /// Needs to be incrementing because you may have more than one specialized
    /// version of a given container type.
    next_ngen_idx: u64,
    local_params: Vec<ExprPtr<'a>>,
    local_indices: Vec<Vec<ExprPtr<'a>>>,
    block_codom: Option<LevelPtr<'a>>,
    is_zero: Option<bool>,
    is_nonzero: Option<bool>,
    ind_consts: Vec<ExprPtr<'a>>,
    rec_uparams: Option<LevelsPtr<'a>>,
    elim_level: Option<LevelPtr<'a>>,
    k_target: Option<bool>,
    majors: Vec<ExprPtr<'a>>,
    motives: Vec<ExprPtr<'a>>,
    minors: Vec<Vec<ExprPtr<'a>>>,
}

impl<'a> InductiveCheckState<'a> {
    /// To be a target for k-like reduction, a type cannot be mutual or nested, must be an inductive
    /// prop, must have only one constructor, and the constructor can take only the type's parameters
    /// as arguments.
    fn init_k_target(&mut self) {
        let is_k_target = self.is_zero.unwrap()
            && self.all_inductives_incl_specialized.len() == 1
            && match self.all_inductives_incl_specialized[0].ctors.as_slice() {
                [only_ctor] => only_ctor.ty.pi_telescope_size() as usize == self.local_params.len(),
                _ => false,
            };
        self.k_target = Some(is_k_target);
    }

    /// Extend the current environment with new constructors, including modifications
    /// to accommodate any temporary declarations that come from nested inductives.
    fn ctors_env_ext(&self, mut env_ext: DeclarMap<'a>) -> DeclarMap<'a> {
        // This will be different from the export file's list if this is a nested.
        for inductive in &self.all_inductives_incl_specialized {
            for (idx, ctor) in inductive.ctors.iter().copied().enumerate() {
                let info = DeclarInfo {
                    name: ctor.name,
                    ty: ctor.ty,
                    uparams: self.uparams,
                };
                let num_params = u16::try_from(self.local_params.len()).unwrap();
                let num_fields = ctor.ty.pi_telescope_size() - num_params;
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
    ///
    /// Then assert that any of the inductive types in the temporary extension
    /// which are also in the export file are `def_eq` to those in the export file.
    fn ind_tys_env_ext(&self) -> DeclarMap<'a> {
        // This will be different from the export file's list if this is a nested.
        let is_nested = !self.nested_to_unspecialized_ty.is_empty();
        let all_ind_names: Arc<[NamePtr]> = self
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
        info_uparams: LevelsPtr<'a>,
        num_params: u16,
        new_tys: Vec<IndTyHeader<'a>>,
        local_params: Vec<ExprPtr<'a>>,
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

    fn flat_minors(&self) -> Vec<ExprPtr<'a>> {
        self.minors.iter().flat_map(|v| v.iter().copied()).collect()
    }
}

#[derive(Debug, Clone)]
struct IndTyHeader<'a> {
    name: NamePtr<'a>,
    ty: ExprPtr<'a>,
    ctors: Vec<CtorHeader<'a>>,
}

#[derive(Debug, Clone, Copy)]
struct CtorHeader<'a> {
    name: NamePtr<'a>,
    ty: ExprPtr<'a>,
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    fn assert_block_recursor_names(
        &mut self,
        ind_name: NamePtr<'t>,
        expected: impl IntoIterator<Item = NamePtr<'t>>,
    ) {
        let expected: FxHashSet<_> = expected.into_iter().collect();
        let &(start, size) = self
            .ctx
            .export_file
            .mutual_block_sizes
            .get(&ind_name)
            .expect("missing inductive block boundaries");
        let imported: FxHashSet<_> = (start..start + size)
            .filter_map(|idx| self.ctx.export_file.declars.get_index(idx))
            .filter_map(|(_, declar)| match declar {
                Declar::Recursor(recursor) => Some(recursor.info.name),
                _ => None,
            })
            .collect();
        ensure_eq!(
            imported,
            expected,
            "imported inductive block contains an underived recursor"
        );
    }

    fn base_recursor_names(&mut self, ind_names: &[NamePtr<'t>]) -> FxHashSet<NamePtr<'t>> {
        let rec = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
        ind_names
            .iter()
            .map(|name| self.ctx.str(*name, rec))
            .collect()
    }

    fn assert_imported_expr_matches(&mut self, imported: ExprPtr<'t>, reconstructed: ExprPtr<'t>) {
        self.tc_cache.clear();
        ensure!(
            self.def_eq_core(imported, reconstructed),
            "imported recursor rule does not match the reconstructed rule"
        );
    }

    fn get_local_params(
        &mut self,
        e: ExprPtr<'t>,
        num_params: u16,
    ) -> (Vec<ExprPtr<'t>>, ExprPtr<'t>) {
        let mut depth = 0u32;
        let mut params = Vec::with_capacity(num_params as usize);
        let mut cur = self.value_of(e);
        for _ in 0..num_params {
            let Some(Value::Pi { domain, body, .. }) = self.force_pi(depth, cur) else {
                reject!("exhausted telescope early")
            };
            let domain = *domain;
            let binder_type = self.quote(depth, domain);
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
            params.push(binder_type);
        }
        let rest = self.quote(depth, cur);
        (params, rest)
    }

    fn param_var(&mut self, st: &InductiveCheckState<'t>, offset: u16, i: u16) -> ExprPtr<'t> {
        self.ctx.mk_var(offset + st.num_params() - 1 - i)
    }

    fn param_vars(&mut self, st: &InductiveCheckState<'t>, offset: u16) -> Vec<ExprPtr<'t>> {
        (0..st.num_params())
            .map(|i| self.param_var(st, offset, i))
            .collect()
    }

    fn mk_pis_dep(
        &mut self,
        binders: &[ExprPtr<'t>],
        gap: u16,
        mut body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        for (i, ty) in binders.iter().copied().enumerate().rev() {
            let ty = self
                .ctx
                .lift(ty, u16::try_from(i).expect("telescope exceeds u16"), gap);
            body = self.ctx.mk_pi(ty, body);
        }
        body
    }

    fn mk_pis_flat(&mut self, binders: &[ExprPtr<'t>], mut body: ExprPtr<'t>) -> ExprPtr<'t> {
        for (i, ty) in binders.iter().copied().enumerate().rev() {
            let ty = self
                .ctx
                .lift(ty, 0, u16::try_from(i).expect("telescope exceeds u16"));
            body = self.ctx.mk_pi(ty, body);
        }
        body
    }

    fn mk_lambdas_dep(
        &mut self,
        binders: &[ExprPtr<'t>],
        gap: u16,
        mut body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        for (i, ty) in binders.iter().copied().enumerate().rev() {
            let ty = self
                .ctx
                .lift(ty, u16::try_from(i).expect("telescope exceeds u16"), gap);
            body = self.ctx.mk_lambda(ty, body);
        }
        body
    }

    fn mk_lambdas_flat(&mut self, binders: &[ExprPtr<'t>], mut body: ExprPtr<'t>) -> ExprPtr<'t> {
        for (i, ty) in binders.iter().copied().enumerate().rev() {
            let ty = self
                .ctx
                .lift(ty, 0, u16::try_from(i).expect("telescope exceeds u16"));
            body = self.ctx.mk_lambda(ty, body);
        }
        body
    }

    fn header_of_ty(&self, t: &InductiveData<'t>) -> IndTyHeader<'t> {
        fn header_of_ctor<'t>(t: &ConstructorData<'t>) -> CtorHeader<'t> {
            CtorHeader {
                name: t.info.name,
                ty: t.info.ty,
            }
        }
        let ctors = t
            .all_ctor_names
            .iter()
            .map(|ctor_name| header_of_ctor(self.env.get_constructor(*ctor_name).unwrap()))
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
    fn collect_unmodified_mutuals(&self, t_from_file: &InductiveData<'t>) -> Vec<IndTyHeader<'t>> {
        // Get all of the mutual inductives, but don't re-insert the base type.
        t_from_file
            .all_ind_names
            .iter()
            .map(|n| self.header_of_ty(self.env.get_inductive(*n).unwrap()))
            .collect()
    }

    fn mk_unique_name(&mut self, n: NamePtr<'t>, st: &mut InductiveCheckState<'t>) -> NamePtr<'t> {
        for idx in st.next_ngen_idx..u64::MAX {
            let tester = self.ctx.append_index_after(n, idx);
            if self.env.get_old_declar(tester).is_none() {
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
