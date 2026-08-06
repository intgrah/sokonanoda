use crate::value::{Closure, RigidHead, Value, S, V};
use crate::env::{ConstructorData, Declar, DeclarInfo, DeclarMap, InductiveData, RecRule, RecursorData};
use crate::expr::{BinderStyle, Expr::*};
use crate::tc::{TypeChecker};
use crate::util::{ExportFile, ExprPtr, FxIndexMap, LevelPtr, LevelsPtr, NamePtr, TcCtx};
use std::sync::Arc;

type Bndr<'a> = (NamePtr<'a>, BinderStyle, ExprPtr<'a>);

impl<'t, 'p: 't> ExportFile<'p> {
    pub(crate) fn check_inductive_declar(
        &'t self,
        ctx: &mut TcCtx<'t, 'p>,
        cache: &mut crate::util::TcCache<'t, 't>,
        arena: &'t bumpalo::Bump,
        d: &Declar<'t>,
    ) {
        let (ind, env_limit) = match d {
            Declar::Inductive(ind) => {
                let is_recursive = {
                    let mut found = false;
                    'outer: for ctor_name in ind.all_ctor_names.iter() {
                        match self.declars.get(ctor_name).unwrap() {
                            Declar::Constructor(ctor_data @ ConstructorData { .. }) => {
                                let mut ctor_ty = ctor_data.info.ty;
                                while let Pi { binder_type, body, .. } = ctx.read_expr(ctor_ty) {
                                    if ctx.find_const(binder_type, |n| ind.all_ind_names.iter().any(|nn| n == *nn)) {
                                        found = true;
                                        break 'outer
                                    }
                                    ctor_ty = body;
                                }
                            }
                            _ => panic!(),
                        }
                    }
                    found
                };
                assert_eq!(ind.is_recursive, is_recursive);
                let (start, size) = self.mutual_block_sizes.get(&ind.info.name).unwrap();
                (ind, crate::env::EnvLimit::ByIndex(start + size))
            }
            _ => panic!("expected inductive")
        };
        {
            // The **unmodified** types and constructors for all of the types in this mutual block.
            let unmodified_tys_ctors = ctx.with_tc(env_limit, arena, cache, |tc| {
                tc.check_declar_info_v(d);
                tc.collect_unmodified_mutuals(ind)
            });

            // Initialize the big chunk of state used throughout the process of checking
            // this inductive declaration.
            let mut st = ctx.with_tc(env_limit, arena, cache, |tc| tc.specialize_nested(ind, unmodified_tys_ctors.clone()));

            // Check the (potentially modified) inductive specs against the base environment.
            ctx.with_tc(env_limit, arena, cache, |tc| tc.check_inductive_specs(&mut st));

            // The first temporary environment extension, containing any specialized
            // types to deal with nested inductives.
            let ind_ty_ext1 = ctx.mk_ind_tys_env_ext(&st);

            // Check the constructors against the environment with the base extension.
            ctx.with_tc_and_env_ext(&ind_ty_ext1, env_limit, arena, cache, |tc| {
                for ind in st.all_inductives_incl_specialized.iter() {
                    for ctor in ind.ctors.iter() {
                        tc.check_ctor(&st, ind.name, ctor.ty)
                    }
                }
            });

            // The second temporary environment extension, which also includes the constructors.
            let ctor_extension = ctx.mk_ctors_env_ext(&st, ind_ty_ext1);

            // The constructed recursors and rec rules
            let recursors = ctx.with_tc_and_env_ext(&ctor_extension, env_limit, arena, cache, |tc| {
                tc.mk_elim_level(&mut st);
                tc.init_k_target(&mut st);
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
                if st.is_nested() {
                    tc.restore_and_check(&st, &unmodified_tys_ctors, &ind.all_ind_names);
                } else {
                    // Do the definitional equality assertions of new/old here.
                    tc.assert_nonnested_tys_def_eq(ind, &st);
                    tc.assert_nonnested_ctors_def_eq(&st);
                    tc.assert_nonnested_recursors_def_eq(&st, &recursors);
                }
            })
        }
    }
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    /// Extend the current environment with the inductive specifications,
    /// including modifications to accommodate any temporary declarations
    /// that come from nested inductives.
    ///
    /// Then assert that any of the inductive types in the temporary extension
    /// which are also in the export file are def_eq to those in the export file.
    fn mk_ind_tys_env_ext(&mut self, st: &InductiveCheckState<'t>) -> DeclarMap<'t> {
        // This will be different from the export file's list if this is a nested.
        let is_nested = !st.nested_to_unspecialized_ty.is_empty();
        let all_ind_names: Arc<[NamePtr]> = st.all_inductives_incl_specialized.iter().map(|x| x.name).collect();
        let mut env_extension = crate::util::new_fx_index_map();
        for (idx, inductive) in st.all_inductives_incl_specialized.iter().enumerate() {
            let t = Declar::Inductive(InductiveData {
                info: DeclarInfo { name: inductive.name, ty: inductive.ty, uparams: st.uparams },
                is_nested,
                is_recursive: false,
                num_params: u16::try_from(st.local_params.len()).unwrap(),
                num_indices: u16::try_from((st.local_indices[idx]).len()).unwrap(),
                all_ind_names: all_ind_names.clone(),
                all_ctor_names: inductive.ctors.iter().map(|x| x.name).collect(),
            });
            env_extension.insert(inductive.name, t);
        }
        env_extension
    }

    /// Extend the current environment with new constructors, including modifications
    /// to accommodate any temporary declarations that come from nested inductives.
    fn mk_ctors_env_ext(&mut self, nest_st: &InductiveCheckState<'t>, mut env_ext: DeclarMap<'t>) -> DeclarMap<'t> {
        // This will be different from the export file's list if this is a nested.
        for inductive in nest_st.all_inductives_incl_specialized.iter() {
            for (idx, ctor) in inductive.ctors.iter().copied().enumerate() {
                let info = DeclarInfo { name: ctor.name, ty: ctor.ty, uparams: nest_st.uparams };
                let num_params = u16::try_from(nest_st.local_params.len()).unwrap();
                let num_fields = self.pi_telescope_size(ctor.ty) - num_params;
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
    local_params: Vec<Bndr<'a>>,
    local_indices: Vec<Vec<Bndr<'a>>>,
    block_codom: Option<LevelPtr<'a>>,
    is_zero: Option<bool>,
    is_nonzero: Option<bool>,
    ind_consts: Vec<ExprPtr<'a>>,
    rec_uparams: Option<LevelsPtr<'a>>,
    elim_level: Option<LevelPtr<'a>>,
    k_target: Option<bool>,
    majors: Vec<Bndr<'a>>,
    motives: Vec<Bndr<'a>>,
    minors: Vec<Vec<Bndr<'a>>>,
}

impl<'a> InductiveCheckState<'a> {
    fn new(
        info_uparams: LevelsPtr<'a>,
        num_params: u16,
        new_tys: Vec<IndTyHeader<'a>>,
        local_params: Vec<Bndr<'a>>,
    ) -> Self {
        Self {
            nested_to_unspecialized_ty: crate::util::new_fx_index_map(),
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
    fn is_nested(&self) -> bool { !self.nested_to_unspecialized_ty.is_empty() }

    fn num_params(&self) -> u16 { u16::try_from(self.local_params.len()).expect("parameter count exceeds u16") }

    fn num_motives(&self) -> u16 { u16::try_from(self.motives.len()).expect("motive count exceeds u16") }

    fn minor_base(&self) -> u16 { self.num_params() + self.num_motives() }

    fn flat_minors(&self) -> Vec<Bndr<'a>> { self.minors.iter().flat_map(|v| v.iter().copied()).collect() }
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
    fn specialize_nested(
        &mut self,
        t_from_file: &InductiveData<'t>,
        unmodified_tys_ctors: Vec<IndTyHeader<'t>>,
    ) -> InductiveCheckState<'t> {
        let (local_params, _instd) = self.get_local_params(unmodified_tys_ctors[0].ty, t_from_file.num_params);

        let mut st = InductiveCheckState::new(
            t_from_file.info.uparams,
            u16::try_from(local_params.len()).unwrap(),
            unmodified_tys_ctors,
            local_params,
        );
        // Collect the new `NestedNewType` items constructed from any actually nested inductives.
        self.specialize_nested_aux(&mut st);

        for ind in st.all_inductives_incl_specialized.iter() {
            assert_eq!(self.ctx.num_loose_bvars(ind.ty), 0);
            for c in ind.ctors.iter() {
                assert_eq!(self.ctx.num_loose_bvars(c.ty), 0);
            }
        }
        st
    }

    /// This function does two important things, and it sort of needs to do them together.
    ///
    /// 1. it adds any new specialized inductive types needed to handle nested inductives to the state.
    /// For example, in the declaration for `Lean.Syntax`, adding `_nested.Array_X` to
    /// `st.all_inductives_incl_specialized`.
    ///
    /// 2. it goes through the constructors of all the inductives, including the newly added specialized
    /// ones, and finds instances of nested types, replacing them in with instances of the specialized types.
    /// For example, replacing the occurrence of `Array Syntax` in the `Lean.Syntax.node` constructor
    /// with `_nested.Array_N`.
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
            for adjusted_ctor in (st.all_inductives_incl_specialized[i].clone()).ctors.iter() {
                let (ctor_local_params, ctor_type_instd) = self.get_local_params(adjusted_ctor.ty, st.num_params());
                let replaced_ctor_wo_params = self.replace_all_nested(ctor_type_instd, st, 0);
                let replaced_ctor_w_params = self.mk_pis_dep(ctor_local_params.as_slice(), 0, replaced_ctor_wo_params);
                new_ctors_for_i.push(CtorHeader { name: adjusted_ctor.name, ty: replaced_ctor_w_params });
            }
            // update the constructors for the inductive `i` with the replaced constructors.
            match st.all_inductives_incl_specialized.get_mut(i) {
                // e.g. replace the base `Syntax.node` with the updated one that replaces `Array`.
                Some(old) => {
                    let _ = std::mem::replace(&mut old.ctors, new_ctors_for_i);
                }
                None => panic!("inductive type {} is missing", i),
            }
            i += 1;
        }
    }

    fn get_local_params(&mut self, e: ExprPtr<'t>, num_params: u16) -> (Vec<Bndr<'t>>, ExprPtr<'t>) {
        let mut depth = 0u32;
        let mut params = Vec::with_capacity(num_params as usize);
        let mut cur = self.value_of(e);
        for _ in 0..num_params {
            let Some(Value::Pi { binder_name, binder_style, domain, body, .. }) = self.force_pi(depth, cur) else {
                panic!("exhausted telescope early")
            };
            let (binder_name, binder_style, domain) = (*binder_name, *binder_style, *domain);
            let binder_type = self.quote(depth, domain);
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
            params.push((binder_name, binder_style, binder_type));
        }
        let rest = self.quote(depth, cur);
        (params, rest)
    }

    fn param_var(&mut self, st: &InductiveCheckState<'t>, offset: u16, i: u16) -> ExprPtr<'t> {
        self.ctx.mk_var(offset + st.num_params() - 1 - i)
    }

    fn param_vars(&mut self, st: &InductiveCheckState<'t>, offset: u16) -> Vec<ExprPtr<'t>> {
        (0..st.num_params()).map(|i| self.param_var(st, offset, i)).collect()
    }

    fn mk_pis_dep(&mut self, binders: &[Bndr<'t>], gap: u16, mut body: ExprPtr<'t>) -> ExprPtr<'t> {
        for (i, (binder_name, binder_style, ty)) in binders.iter().copied().enumerate().rev() {
            let ty = self.ctx.lift(ty, u16::try_from(i).expect("telescope exceeds u16"), gap);
            body = self.ctx.mk_pi(binder_name, binder_style, ty, body);
        }
        body
    }

    fn mk_pis_flat(&mut self, binders: &[Bndr<'t>], mut body: ExprPtr<'t>) -> ExprPtr<'t> {
        for (i, (binder_name, binder_style, ty)) in binders.iter().copied().enumerate().rev() {
            let ty = self.ctx.lift(ty, 0, u16::try_from(i).expect("telescope exceeds u16"));
            body = self.ctx.mk_pi(binder_name, binder_style, ty, body);
        }
        body
    }

    fn mk_lambdas_dep(&mut self, binders: &[Bndr<'t>], gap: u16, mut body: ExprPtr<'t>) -> ExprPtr<'t> {
        for (i, (binder_name, binder_style, ty)) in binders.iter().copied().enumerate().rev() {
            let ty = self.ctx.lift(ty, u16::try_from(i).expect("telescope exceeds u16"), gap);
            body = self.ctx.mk_lambda(binder_name, binder_style, ty, body);
        }
        body
    }

    fn mk_lambdas_flat(&mut self, binders: &[Bndr<'t>], mut body: ExprPtr<'t>) -> ExprPtr<'t> {
        for (i, (binder_name, binder_style, ty)) in binders.iter().copied().enumerate().rev() {
            let ty = self.ctx.lift(ty, 0, u16::try_from(i).expect("telescope exceeds u16"));
            body = self.ctx.mk_lambda(binder_name, binder_style, ty, body);
        }
        body
    }

    /// Check the 0th element of the list of inductive types; this one is different
    /// than the mutuals, because we need to determine the target for the block codom
    /// and some other stuff.
    fn check_inductive_spec_0th(&mut self, uparams: LevelsPtr<'t>, st: &mut InductiveCheckState<'t>) {
        self.tc_cache.clear();
        let (ind_name, ind_ty) = st.all_inductives_incl_specialized.get(0).map(|x| (x.name, x.ty)).unwrap();
        let mut depth = 0u32;
        let mut env = self.empty_env();
        let mut cur = self.value_of(ind_ty);
        let mut indices = Vec::new();
        let mut i = 0;
        while let Some(Value::Pi { binder_name, binder_style, domain, body, .. }) = self.force_pi(depth, cur) {
            let (binder_name, binder_style, domain) = (*binder_name, *binder_style, *domain);
            if i < st.local_params.len() {
                let stored = st.local_params[i].2;
                self.tc_cache.clear();
                let expected = self.eval(depth, env, stored);
                assert!(self.def_eq_at(depth, domain, expected), "def_eq failed");
            } else {
                let binder_type = self.quote(depth, domain);
                indices.push((binder_name, binder_style, binder_type));
            }
            let fresh = self.mk_bvar_hc(depth, domain);
            env = crate::value::env_extend(self.arena, env, fresh);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
            i += 1;
        }
        let block_codom = self.ensure_sort_v(depth, cur);
        let is_nonzero = self.ctx.is_nonzero(block_codom);
        let is_zero = self.ctx.is_zero(block_codom);
        let ind_const = self.ctx.mk_const(ind_name, uparams);

        st.local_indices.push(indices);
        st.block_codom = Some(block_codom);
        st.is_zero = Some(is_zero);
        st.is_nonzero = Some(is_nonzero);
        st.ind_consts.push(ind_const);
    }

    /// Check the rest of the types in a mutual block, ensuring they agree with the base type.
    fn check_inductive_specs_mutual1(&mut self, st: &mut InductiveCheckState<'t>, ind: IndTyHeader<'t>) {
        self.tc_cache.clear();
        let mut depth = 0u32;
        let mut cur = self.value_of(ind.ty);
        let mut indices = Vec::new();
        let mut i = 0;
        while let Some(Value::Pi { binder_name, binder_style, domain, body, .. }) = self.force_pi(depth, cur) {
            let (binder_name, binder_style, domain) = (*binder_name, *binder_style, *domain);
            if i >= st.local_params.len() {
                let binder_type = self.quote(depth, domain);
                indices.push((binder_name, binder_style, binder_type));
            }
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
            i += 1;
        }
        let codom_level = self.ensure_sort_v(depth, cur);
        assert!(self.ctx.eq_antisymm(codom_level, st.block_codom.unwrap()));
        st.local_indices.push(indices);
        st.ind_consts.push(self.ctx.mk_const(ind.name, st.uparams));
    }

    /// This starts by receiving the "full" `InductiveType` specification from the export
    /// file for the actual declaration being checked. It *ALSO* gets the NestedInductiveState,
    /// since the process of checking these also has to deal with the new types created
    /// during the nest procedure.
    fn check_inductive_specs(&mut self, st: &mut InductiveCheckState<'t>) {
        let nbefore = st.all_inductives_incl_specialized.len();
        for i in 0..st.all_inductives_incl_specialized.len() {
            if i == 0 {
                self.check_inductive_spec_0th(st.uparams, st);
                assert_eq!(st.local_indices.len(), 1);
            } else {
                assert_eq!(st.local_indices.len(), i);
                self.check_inductive_specs_mutual1(st, st.all_inductives_incl_specialized[i].clone());
            }
        }
        assert_eq!(st.all_inductives_incl_specialized.len(), nbefore);
        assert_eq!(st.all_inductives_incl_specialized.len(), st.local_indices.len());
    }

    fn check_declared_metadata(&mut self, st: &InductiveCheckState<'t>, unmodified: &[IndTyHeader<'t>]) {
        let num_params = usize::from(st.num_params());
        for (i, header) in unmodified.iter().enumerate() {
            let ind = self.env.get_inductive(&header.name).expect("inductive is not declared");
            assert_eq!(usize::from(ind.num_params), num_params, "inductive declares the wrong number of parameters");
            assert_eq!(
                usize::from(ind.num_indices),
                st.local_indices[i].len(),
                "inductive declares the wrong number of indices"
            );
            assert_eq!(
                ind.all_ctor_names.len(),
                header.ctors.len(),
                "inductive declares the wrong number of constructors"
            );
            for (ctor_idx, ctor) in header.ctors.iter().enumerate() {
                let telescope = self.ctx.pi_telescope_size(ctor.ty) as usize;
                assert!(telescope >= num_params, "constructor telescope is shorter than the parameters");
                let cd = self.env.get_constructor(&ctor.name).expect("constructor is not declared");
                assert_eq!(cd.inductive_name, header.name, "constructor declares the wrong inductive");
                assert_eq!(usize::from(cd.ctor_idx), ctor_idx, "constructor declares the wrong index");
                assert_eq!(usize::from(cd.num_params), num_params, "constructor declares the wrong number of parameters");
                assert_eq!(
                    usize::from(cd.num_fields),
                    telescope - num_params,
                    "constructor declares the wrong number of fields"
                );
            }
            let rec_name = {
                let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
                self.ctx.str(header.name, rec_str_ptr)
            };
            if let Some(rd) = self.env.get_recursor(&rec_name) {
                assert_eq!(rd.is_k, st.k_target.unwrap(), "recursor declares the wrong k-reduction flag");
                assert_eq!(usize::from(rd.num_params), num_params, "recursor declares the wrong number of parameters");
                assert_eq!(
                    usize::from(rd.num_indices),
                    st.local_indices[i].len(),
                    "recursor declares the wrong number of indices"
                );
            }
        }
    }

    fn is_nested_ind_app(
        &mut self,
        st: &InductiveCheckState<'t>,
        e: ExprPtr<'t>,
        offset: u16,
    ) -> Option<InductiveData<'t>> {
        if !(matches!(self.ctx.read_expr(e), App { .. })) {
            return None
        }
        let (_f, name, _levels, args) = self.ctx.unfold_const_apps(self.arena, e)?;
        // If this is an application of an inductive, like `Array A`
        let ind_ty_declar @ InductiveData { num_params, .. } = self.env.get_inductive(&name)?;
        if (*num_params as usize) > args.len() {
            return None
        }
        let mut inner_bvars = false;
        let mut is_nested = false;
        for i in 0..(*num_params as usize) {
            let this_param = args[i];
            if self.ctx.has_loose_bvar_below(this_param, offset) {
                inner_bvars = true;
            }
            if self
                .ctx
                .find_const(this_param, |n| st.all_inductives_incl_specialized.iter().any(|new_ty| new_ty.name == n))
            {
                is_nested = true;
            }
        }
        if !is_nested {
            return None
        }
        if inner_bvars {
            panic!("a nested type may only be applied to the block's parameters")
        }
        Some(ind_ty_declar.clone())
    }

    fn header_of_ty(&self, t: &InductiveData<'t>) -> IndTyHeader<'t> {
        fn header_of_ctor<'t>(t: &ConstructorData<'t>) -> CtorHeader<'t> {
            CtorHeader { name: t.info.name, ty: t.info.ty }
        }
        let ctors = {
            let mut out = Vec::new();
            for ctor_name in t.all_ctor_names.as_ref() {
                out.push(header_of_ctor(self.env.get_constructor(ctor_name).unwrap()));
            }
            out
        };
        IndTyHeader { name: t.info.name, ty: t.info.ty, ctors }
    }

    /// For some exported inductive declaration `T` that has a list of mutual names
    /// `[T, U, .., Z]`, return the `IndTyHeader` elements for `[T, U, .., Z]`, without
    /// any specializations/modifications.
    fn collect_unmodified_mutuals(&self, t_from_file: &InductiveData<'t>) -> Vec<IndTyHeader<'t>> {
        let mut all_inductives = Vec::new();
        // Get all of the mutual inductives, but don't re-insert the base type.
        for n in t_from_file.all_ind_names.iter() {
            let t = self.env.get_inductive(n).unwrap();
            all_inductives.push(self.header_of_ty(t));
        }
        all_inductives
    }

    fn mk_unique_name(&mut self, n: NamePtr<'t>, st: &mut InductiveCheckState<'t>) -> NamePtr<'t> {
        for idx in st.next_ngen_idx..u64::MAX {
            let tester = self.ctx.append_index_after(n, idx);
            if !self.env.get_old_declar(&tester).is_some() {
                st.next_ngen_idx = idx + 1;
                return tester
            }
        }
        panic!("Unable to generate unique name, u64 exhausted")
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
        let (f, i_name, i_levels, args) = self.ctx.unfold_const_apps(self.arena, e).unwrap();
        assert!(nested_container_ty.num_params as usize <= args.len());
        // Reapply the portion of the unfolded applications that is the parameters.
        let i_as = self.ctx.foldl_apps(f, args.iter().copied().take(nested_container_ty.num_params as usize));
        let i_params = self.ctx.lower(i_as, 0, offset);
        let outgoing_param_vars = self.param_vars(st, offset);

        if let Some((aux_i_name, _)) = st.nested_to_unspecialized_ty.iter().find(|(_name, expr)| **expr == i_params) {
            let f = self.ctx.mk_const(*aux_i_name, st.uparams);
            let f = self.ctx.foldl_apps(f, outgoing_param_vars.iter().copied());
            let f =
                self.ctx.foldl_apps(f, (args[(nested_container_ty.num_params as usize)..args.len()]).iter().copied());
            Some(f)
        } else {
            let mut result: Option<ExprPtr> = None;
            // `Array`, `List`, and any mutuals in the appropriate block etc.
            for nested_container_name in nested_container_ty.all_ind_names.iter().copied() {
                // The inductive declaration for the container type, like `Array`
                let InductiveData { info: container_ty_info, all_ctor_names: all_nested_container_ctor_names, .. } =
                    self.env.get_inductive(&nested_container_name)?;
                // `i_levels` is the set of uparams we actually found in the declaration we're checking,
                // so the set of uparams in `Lean.Syntax`, as opposed to the uparam declars for `Array`
                let js = {
                    let base_const = self.ctx.mk_const(nested_container_name, i_levels);
                    self.ctx.foldl_apps(base_const, (args[0..nested_container_ty.num_params as usize]).iter().copied())
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
                    let base = self.ctx.subst_expr_levels(container_ty_info.ty, container_ty_info.uparams, i_levels);
                    let instd =
                        self.ctx.inst_forall_params(base, nested_container_ty.num_params as usize, args.as_slice());
                    let instd = self.ctx.lower(instd, 0, offset);
                    let params = st.local_params.clone();
                    self.mk_pis_dep(params.as_slice(), 0, instd)
                };
                let jsprime = self.ctx.lower(js, 0, offset);
                st.nested_to_unspecialized_ty.insert(aux_nested_container_name, jsprime);
                if nested_container_name == i_name {
                    let f = self.ctx.mk_const(aux_nested_container_name, st.uparams);
                    let f = self.ctx.foldl_apps(f, outgoing_param_vars.iter().copied());
                    let args = &args[nested_container_ty.num_params as usize..args.len()];
                    let f = self.ctx.foldl_apps(f, args.iter().copied());
                    result = Some(f);
                }
                let mut auxj_ctors = Vec::<CtorHeader>::new();
                for j_ctor_name in all_nested_container_ctor_names.iter().copied() {
                    let ConstructorData { info: j_ctor_info, .. } = self.env.get_constructor(&j_ctor_name)?;
                    // Replace `Array.mk` with `_nested.Array_2.mk`
                    let auxj_ctor_name =
                        self.ctx.replace_pfx(j_ctor_name, nested_container_name, aux_nested_container_name);
                    let auxj_ctor_type = self.ctx.subst_expr_levels(j_ctor_info.ty, j_ctor_info.uparams, i_levels);
                    let auxj_ctor_type = self.ctx.inst_forall_params(
                        auxj_ctor_type,
                        nested_container_ty.num_params as usize,
                        args.as_slice(),
                    );
                    let auxj_ctor_type = self.ctx.lower(auxj_ctor_type, 0, offset);
                    let params = st.local_params.clone();
                    let auxj_ctor_type = self.mk_pis_dep(params.as_slice(), 0, auxj_ctor_type);
                    auxj_ctors.push(CtorHeader { name: auxj_ctor_name, ty: auxj_ctor_type })
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

    fn replace_all_nested(&mut self, e: ExprPtr<'t>, st: &mut InductiveCheckState<'t>, offset: u16) -> ExprPtr<'t> {
        // Try to replace locally before traversing into the lower parts.
        if let Some(eprime) = self.replace_if_nested(e, st, offset) {
            eprime
        } else {
            match self.ctx.read_expr(e) {
                Var { .. } | Sort { .. } | Const { .. } | NatLit { .. } | StringLit { .. } => e,
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.replace_all_nested(binder_type, st, offset);
                    let body = self.replace_all_nested(body, st, offset + 1);
                    self.ctx.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.replace_all_nested(binder_type, st, offset);
                    let body = self.replace_all_nested(body, st, offset + 1);
                    self.ctx.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { data: &crate::expr::LetData { binder_name, binder_type, val, body, nondep }, .. } => {
                    let binder_type = self.replace_all_nested(binder_type, st, offset);
                    let val = self.replace_all_nested(val, st, offset);
                    let body = self.replace_all_nested(body, st, offset + 1);
                    self.ctx.mk_let(binder_name, binder_type, val, body, nondep)
                }
                App { fun, arg, .. } => {
                    let fun = self.replace_all_nested(fun, st, offset);
                    let arg = self.replace_all_nested(arg, st, offset);
                    self.ctx.mk_app(fun, arg)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.replace_all_nested(structure, st, offset);
                    self.ctx.mk_proj(ty_name, idx, structure)
                }
            }
        }
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
    fn check_positivity1(&mut self, st: &InductiveCheckState<'t>, cursor: V<'t>, depth0: u32) {
        let mut depth = depth0;
        let mut cur = cursor;
        loop {
            cur = self.force_all(depth, cur);
            if !self.value_has_ind_occ(depth, cur, st.ind_consts.as_ref()) {
                return
            }
            match cur {
                Value::Pi { binder_name, binder_style, domain, body, .. } => {
                    let (binder_name, binder_style, domain, body) = (*binder_name, *binder_style, *domain, *body);
                    if self.value_has_ind_occ(depth, domain, st.ind_consts.as_ref()) {
                        panic!("non-positive occurrence");
                    }
                    let _ = (binder_name, binder_style);
                    let fresh = self.mk_bvar_hc(depth, domain);
                    cur = self.apply_closure(depth + 1, &body, fresh, Some(domain));
                    depth += 1;
                }
                _ => {
                    // We only need to know that it's a valid ind-app for SOMETHING in the block, since
                    // this is only a binder in the constructor, not the end of the telescope.
                    assert!(self.which_valid_ind_app_v(st, depth, cur).is_some());
                    return;
                }
            }
        }
    }


    // For an expression `E` and a list
    // of names `NS`, recursively search through `E` for a `Const { name, levels }`
    // `C`, whose name is ANY of the names in `NS`. If such a `C` exists,
    // return true, else return false.
    //
    // This is used in the formation of inductive types, to determine whether
    // a type is recursive, reflexive, contains only positive occurrences, and
    // has only valid applications.
    fn has_ind_occ(&mut self, e: ExprPtr<'t>, haystack: &[ExprPtr<'t>]) -> bool {
        let f = |nptr| {
            haystack.iter().copied().any(|c| match self.ctx.read_expr(c) {
                Const { name, .. } => name == nptr,
                _ => panic!(),
            })
        };

        self.ctx.find_const(e, f)
    }

    fn get_i_indices_at(
        &mut self,
        st: &InductiveCheckState<'t>,
        ind_ty_app: ExprPtr<'t>,
        v: V<'t>,
        depth: u32,
    ) -> (usize, Vec<ExprPtr<'t>>) {
        let valid_app_idx = self.which_valid_ind_app_v(st, depth, v).unwrap();
        let (_, mut ctor_args_wo_params) = self.ctx.unfold_apps_stack(self.arena, ind_ty_app);
        // Compensate for stack-like unfold
        for _ in 0..st.local_params.len() {
            ctor_args_wo_params.pop();
        }
        (valid_app_idx, ctor_args_wo_params.iter().copied().collect())
    }

    fn inst_params_at(&mut self, e: ExprPtr<'t>, num_params: usize, depth: u16) -> ExprPtr<'t> {
        let n = u16::try_from(num_params).expect("parameter count exceeds u16");
        let substs: Vec<ExprPtr<'t>> = (0..n).map(|j| self.ctx.mk_var(depth + n - 1 - j)).collect();
        self.ctx.inst_open(e, substs.as_slice())
    }

    fn value_has_ind_occ(&mut self, depth: u32, v: V<'t>, haystack: &[ExprPtr<'t>]) -> bool {
        let v = self.force_thunk(depth, v);
        let key = v as *const Value<'t> as usize;
        if let Some(&b) = self.tc_cache.ind_occ_cache.get(&key) {
            return b;
        }
        let r = match v {
            Value::Sort { .. } | Value::NatLit { .. } | Value::StrLit { .. } => false,
            Value::Rigid { head, spine, .. } => {
                let head_hit = match *head {
                    RigidHead::BVar(_, ty) => self.value_has_ind_occ(depth, ty, haystack),
                    RigidHead::Axiom(n, _)
                    | RigidHead::Ctor(n, _)
                    | RigidHead::Recursor(n, _)
                    | RigidHead::QuotConst(n, _)
                    | RigidHead::Inductive(n, _) => self.name_is_ind_occ(n, haystack),
                };
                head_hit || self.spine_has_ind_occ(depth, spine, haystack)
            }
            Value::Unfold { head, spine, .. } =>
                self.name_is_ind_occ(head.name, haystack) || self.spine_has_ind_occ(depth, spine, haystack),
            Value::Lam { body, .. } => {
                let dom = self.lam_domain(depth, v);
                let body = *body;
                self.value_has_ind_occ(depth, dom, haystack) || self.closure_has_ind_occ(depth, &body, haystack)
            }
            Value::Pi { domain, body, .. } => {
                let (domain, body) = (*domain, *body);
                self.value_has_ind_occ(depth, domain, haystack)
                    || self.closure_has_ind_occ(depth, &body, haystack)
            }
            Value::Thunk { .. } => unreachable!("ind occurs: thunk after force"),
        };
        self.tc_cache.ind_occ_cache.insert(key, r);
        r
    }

    fn name_is_ind_occ(&self, n: NamePtr<'t>, haystack: &[ExprPtr<'t>]) -> bool {
        haystack.iter().copied().any(|c| match self.ctx.read_expr(c) {
            Const { name, .. } => name == n,
            _ => panic!(),
        })
    }

    fn spine_has_ind_occ(&mut self, depth: u32, spine: S<'t>, haystack: &[ExprPtr<'t>]) -> bool {
        let mut cur = spine;
        while let crate::value::Spine::Snoc { prev, elim, .. } = cur {
            if let crate::value::ElimView::App(a) = elim.view() {
                if self.value_has_ind_occ(depth, a, haystack) {
                    return true
                }
            }
            cur = prev;
        }
        false
    }

    fn closure_has_ind_occ(&mut self, depth: u32, clo: &Closure<'t>, haystack: &[ExprPtr<'t>]) -> bool {
        if self.has_ind_occ(clo.body, haystack) {
            return true
        }
        let nlb = clo.body.num_loose_bvars();
        let mask = clo.body.as_ref().fv_mask();
        for idx in 0..nlb {
            if idx < 64 && (mask >> idx) & 1 == 0 {
                continue
            }
            if let Some(slot) = clo.env.lookup(idx) {
                if self.value_has_ind_occ(depth, slot, haystack) {
                    return true
                }
            }
        }
        false
    }

    fn is_bvar_at(v: V<'t>, level: u32) -> bool {
        matches!(v, Value::Rigid { head: RigidHead::BVar(l, _), spine, .. } if *l == level && spine.is_empty())
    }

    fn which_valid_ind_app_v(&mut self, st: &InductiveCheckState<'t>, depth: u32, v: V<'t>) -> Option<usize> {
        let f = self.force_all(depth, v);
        let (name, levels, spine) = match f {
            Value::Rigid { head: RigidHead::Inductive(n, ls), spine, .. } => (*n, *ls, *spine),
            _ => return None,
        };
        let pos = st.ind_consts.iter().copied().position(|x| match self.ctx.read_expr(x) {
            Const { name: n, .. } => n == name,
            _ => panic!(),
        })?;
        let expected_levels = match self.ctx.read_expr(st.ind_consts[pos]) {
            Const { levels, .. } => levels,
            _ => return None,
        };
        if !self.ctx.eq_antisymm_many(levels, expected_levels) {
            return None
        }
        let num_params = st.local_params.len();
        if spine.len() as usize != num_params + st.local_indices[pos].len() {
            return None
        }
        let args = self.spine_apps(depth, spine)?;
        for i in 0..num_params {
            if !Self::is_bvar_at(args[i], u32::try_from(i).expect("parameter count exceeds u32")) {
                return None
            }
        }
        for ix in &args[num_params..] {
            if self.value_has_ind_occ(depth, ix, &st.ind_consts) {
                return None
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
            Value::Rigid { head: RigidHead::Inductive(n, _), .. } => *n,
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
            let Some(Value::Pi { domain, body, .. }) = self.weak_pi(depth, cur) else { panic!() };
            let domain = *domain;
            let expected = self.eval(depth, env, st.local_params[i].2);
            assert!(self.def_eq_at(depth, domain, expected), "def_eq failed");
            let fresh = self.mk_bvar_hc(depth, domain);
            env = crate::value::env_extend(self.arena, env, fresh);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
        }
        // Non-param constructor args.
        while let Some(Value::Pi { domain, body, .. }) = self.weak_pi(depth, cur) {
            let domain = *domain;
            let s = self.level_of_type(depth, domain).expect("constructor argument is not a type");
            // The inductive being constructed either has to be a `Prop`,
            // or the constructor argument's type has to be <= the inductive's
            // type.
            if !(st.is_zero.unwrap() || self.ctx.leq(s, st.block_codom.unwrap())) {
                panic!("Constructor argument was too large for the corresponding inductive type")
            }

            // Assert that there are no non-positive occurrences in the constructor.
            self.check_positivity1(st, domain, depth);
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
        }
        // The end of the constructor has to be of the form `parentIndConst params* indices*`
        // as in `List A` or `Nat.le x y`
        assert!(self.is_valid_ind_app_v(st, parent_ind_name, depth, cur))
    }

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
    fn large_elim_test_aux(&mut self, ctor_type_cursor: ExprPtr<'t>, mut rem_params: usize) -> bool {
        self.tc_cache.clear();
        let mut depth = 0u32;
        let mut cur = self.value_of(ctor_type_cursor);
        let mut non_prop_levels: Vec<u32> = Vec::new();
        loop {
            match self.weak_pi(depth, cur) {
                Some(Value::Pi { domain, body, .. }) => {
                    let domain = *domain;
                    let fresh = self.mk_bvar_hc(depth, domain);
                    let level = depth;
                    cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
                    depth += 1;
                    if rem_params != 0 {
                        rem_params -= 1;
                    } else if !self.is_prop_type(depth, domain) {
                        non_prop_levels.push(level);
                    }
                }
                _ => break,
            }
        }

        let non_prop_ctor_telescope_elems: Vec<ExprPtr<'t>> =
            non_prop_levels.iter().map(|l| self.ctx.mk_var(u16::try_from(depth - 1 - l).expect("depth exceeds u16"))).collect();
        let end_of_telescope = self.quote(depth, cur);
        let (_, ind_ty_params_and_indices) = self.ctx.unfold_apps(self.arena, end_of_telescope);

        // Check whether `non_prop_ctor_telescope_elems` is a subset of
        // `ind_ty params ++ ind_ty indices`
        //
        // if the list of non-prop constructor args is NOT a subset of
        // the exprs being applied to the inductive (which is params + indices)
        // then we can say that this type only eliminates into Prop/Sort 0
        non_prop_ctor_telescope_elems.iter().all(|arg| ind_ty_params_and_indices.contains(arg))
    }

    fn large_elim_test(&mut self, st: &InductiveCheckState<'t>) -> bool {
        if st.is_nonzero.unwrap() {
            // If our inductive is in `Type <n>`, it's large eliminating
            return true
        }

        match st.all_inductives_incl_specialized.as_slice() {
            [] => panic!("inductive declaration with no types declared"),
            [ind_ty] => {
                match ind_ty.ctors.as_slice() {
                    // This type is an empty prop (has no constructors)
                    [] => true,
                    // At this point, we know that we're dealing with an inductive that...
                    // 1. is not a mutual inductive (ind_types = 1)
                    // 2. is an inductive proposition (because its result sort is Prop/0)
                    // 3. has one and only one constructor
                    [ctor] => self.large_elim_test_aux(ctor.ty, st.local_params.len()),
                    // More than one constructor; no large elimination.
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn gen_elim_level(&mut self, st: &InductiveCheckState<'t>) -> NamePtr<'t> {
        let p = self.ctx.str1("u");
        if !self.ctx.contains_param(st.uparams, p) {
            return p
        }
        // Lean's pretty printer starts at 1 for universes.
        let mut i = 1u64;
        loop {
            let candidate = self.ctx.append_index_after(p, i);
            if self.ctx.contains_param(st.uparams, candidate) {
                i += 1;
            } else {
                return candidate
            }
        }
    }

    fn mk_elim_level(&mut self, st: &mut InductiveCheckState<'t>) {
        if self.large_elim_test(st) {
            let elim_level = self.gen_elim_level(st);
            let elim_level = self.ctx.param(elim_level);
            // Extra work since you want the new thing at the front of the vector (in position 0)
            let rec_levels = {
                let mut base = vec![elim_level];
                for l in self.ctx.read_levels(st.uparams).iter().copied() {
                    base.push(l)
                }
                self.ctx.alloc_levels(&base)
            };
            st.rec_uparams = Some(rec_levels);
            st.elim_level = Some(elim_level);
        } else {
            // If this is not a large eliminating type, the elim level can only be zero,
            // and the only uparams for the recursor are those of the inductive spec.
            st.elim_level = Some(self.ctx.zero());
            st.rec_uparams = Some(st.uparams);
        };
    }

    /// To be a target for k-like reduction, a type cannot be mutual or nested, must be an inductive
    /// prop, must have only one constructor, and the constructor can take only the type's parameters
    /// as arguments.
    fn init_k_target(&mut self, st: &mut InductiveCheckState<'t>) {
        let is_k_target = st.is_zero.unwrap()
            && st.all_inductives_incl_specialized.len() == 1
            && match st.all_inductives_incl_specialized[0].ctors.as_slice() {
                [only_ctor] => self.ctx.pi_telescope_size(only_ctor.ty) as usize == st.local_params.len(),
                _ => false,
            };
        st.k_target = Some(is_k_target);
    }

    fn mk_majors(&mut self, st: &mut InductiveCheckState<'t>) {
        for (idx, ind_const) in st.ind_consts.iter().copied().enumerate() {
            let num_indices = u16::try_from(st.local_indices[idx].len()).expect("index count exceeds u16");
            let param_vars = self.param_vars(st, num_indices);
            let index_vars: Vec<ExprPtr<'t>> = (0..num_indices).map(|k| self.ctx.mk_var(num_indices - 1 - k)).collect();
            let mut ty = self.ctx.foldl_apps(ind_const, param_vars.into_iter());
            ty = self.ctx.foldl_apps(ty, index_vars.into_iter());
            let t = self.ctx.str1("t");
            st.majors.push((t, BinderStyle::Default, ty));
        }
    }

    fn mk_motive_dep(&mut self, st: &InductiveCheckState<'t>, ind_type_idx: usize) -> Bndr<'t> {
        let elim_sort = self.ctx.mk_sort(st.elim_level.unwrap());
        let major = st.majors[ind_type_idx];
        let w_major = self.ctx.mk_pi(major.0, major.1, major.2, elim_sort);
        let indices = st.local_indices[ind_type_idx].clone();
        let motive_type = self.mk_pis_dep(indices.as_slice(), 0, w_major);
        let motive_name_base = self.ctx.str1("motive");
        let motive_name = if st.all_inductives_incl_specialized.len() > 1 {
            // Lean uses 1-based indexing for these, so we try to match for the pretty printer output.
            self.ctx.append_index_after(motive_name_base, ind_type_idx as u64 + 1)
        } else {
            motive_name_base
        };

        (motive_name, BinderStyle::Implicit, motive_type)
    }

    fn mk_motives(&mut self, st: &mut InductiveCheckState<'t>) {
        debug_assert_eq!(st.local_indices.len(), st.ind_consts.len());
        debug_assert_eq!(st.majors.len(), st.ind_consts.len());
        for i in 0..st.ind_consts.len() {
            st.motives.push(self.mk_motive_dep(st, i));
        }
    }

    fn is_rec_argument_v(&mut self, st: &InductiveCheckState<'t>, cursor: V<'t>, depth0: u32) -> Option<usize> {
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
    ) -> (ExprPtr<'t>, Vec<(NamePtr<'t>, BinderStyle, ExprPtr<'t>)>, V<'t>, u32) {
        let mut depth = depth0;
        let mut cur = cursor;
        let mut xs = Vec::new();
        while let Some(Value::Pi { binder_name, binder_style, domain, body, .. }) = self.force_pi(depth, cur) {
            let (binder_name, binder_style, domain) = (*binder_name, *binder_style, *domain);
            let dom_e = self.quote(depth, domain);
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
            xs.push((binder_name, binder_style, dom_e));
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
    ) -> (ExprPtr<'t>, V<'t>, u32, Vec<Bndr<'t>>, Vec<(usize, V<'t>)>) {
        let mut all_args: Vec<Bndr<'t>> = Vec::new();
        let mut rec_positions = Vec::new();
        self.tc_cache.clear();
        let mut depth = depth0;
        let mut cur = self.value_of(ctor_type_cursor);
        for i in 0..st.local_params.len() {
            let Some(Value::Pi { domain, body, .. }) = self.weak_pi(depth, cur) else { panic!() };
            let domain = *domain;
            let lv = self.mk_bvar_hc(u32::try_from(i).expect("parameter count exceeds u32"), domain);
            cur = self.apply_closure(depth, body, lv, Some(domain));
        }
        while let Some(Value::Pi { binder_name, binder_style, domain, body, .. }) = self.weak_pi(depth, cur) {
            let (binder_name, binder_style, domain) = (*binder_name, *binder_style, *domain);
            let binder_type = self.quote(depth, domain);
            let is_rec = self.is_rec_argument_v(st, domain, depth).is_some();
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            if is_rec {
                rec_positions.push((all_args.len(), domain));
            }
            all_args.push((binder_name, binder_style, binder_type));
            depth += 1;
        }
        let end = self.quote(depth, cur);
        (end, cur, depth, all_args, rec_positions)
    }

    fn handle_rec_args_minor(
        &mut self,
        st: &InductiveCheckState<'t>,
        ctor_idx: usize,
        rec_args: &[(usize, V<'t>)],
        ctor_args_base: u32,
        base_depth: u32,
    ) -> Vec<Bndr<'t>> {
        let mut out = Vec::new();
        for (i, (pos, dom_v)) in rec_args.iter().copied().enumerate() {
            self.tc_cache.clear();
            let here = base_depth + u32::try_from(i).expect("too many recursive arguments");
            let (arg_ty, xs, arg_v, arg_depth) = self.handle_rec_args_aux(dom_v, here);
            let (ind_ty_idx, applied_indices) = self.get_i_indices_at(st, arg_ty, arg_v, arg_depth);
            let n = u16::try_from(xs.len()).expect("telescope exceeds u16");
            let total = u16::try_from(arg_depth).expect("depth exceeds u16");
            let motive_level = u16::try_from(ind_ty_idx).expect("motive count exceeds u16") + st.num_params();
            let motive = self.ctx.mk_var(total - 1 - motive_level);
            let arg_level = u16::try_from(ctor_args_base).expect("depth exceeds u16")
                + u16::try_from(pos).expect("position exceeds u16");
            let x_vars: Vec<ExprPtr<'t>> = (0..n).map(|j| self.ctx.mk_var(n - 1 - j)).collect();
            let rec_arg_var = self.ctx.mk_var(total - 1 - arg_level);
            let motive_base = {
                let lhs = self.ctx.foldl_apps(motive, applied_indices.into_iter().rev());
                let u_app = self.ctx.foldl_apps(rec_arg_var, x_vars.iter().copied());
                self.ctx.mk_app(lhs, u_app)
            };
            let v_i_ty = self.mk_pis_dep(xs.as_slice(), 0, motive_base);
            let v_name = self.ctx.str1("v");
            // rec_arg often has a hygienic name
            let v_name = self.ctx.append_index_after(v_name, ctor_idx as u64);
            let v_name = self.ctx.append_index_after(v_name, i as u64);
            out.push((v_name, BinderStyle::Default, v_i_ty));
        }
        out
    }

    fn mk_minors1group(&mut self, st: &InductiveCheckState<'t>, ctors: &[CtorHeader<'t>]) -> Vec<Bndr<'t>> {
        let mut out = Vec::new();
        let base = u32::from(st.minor_base());
        for (ctor_idx, ctor) in ctors.iter().copied().enumerate() {
            let (stripd, stripd_v, args_depth, all_ctor_args, rec_ctor_args) =
                self.sep_nonrec_rec_ctor_args(st, ctor.ty, base);
            let (ind_ty_idx, applied_indices) = self.get_i_indices_at(st, stripd, stripd_v, args_depth);
            let v = self.handle_rec_args_minor(st, ctor_idx, rec_ctor_args.as_slice(), base, args_depth);
            let n_args = u16::try_from(all_ctor_args.len()).expect("telescope exceeds u16");
            let n_v = u16::try_from(v.len()).expect("telescope exceeds u16");
            let total = u16::try_from(args_depth).expect("depth exceeds u16") + n_v;
            let motive_level = u16::try_from(ind_ty_idx).expect("motive count exceeds u16") + st.num_params();
            let motive = self.ctx.mk_var(total - 1 - motive_level);
            let arg_vars: Vec<ExprPtr<'t>> =
                (0..n_args).map(|j| self.ctx.mk_var(total - 1 - (st.minor_base() + j))).collect();
            let param_vars = self.param_vars(st, total - st.num_params());
            let c_app0 = {
                let rhs = self.ctx.mk_const(ctor.name, st.uparams);
                let rhs = self.ctx.foldl_apps(rhs, param_vars.into_iter());
                self.ctx.foldl_apps(rhs, arg_vars.iter().copied())
            };
            let shifted_indices: Vec<ExprPtr<'t>> =
                applied_indices.into_iter().map(|e| self.ctx.lift(e, 0, n_v)).collect();
            let c_app = self.ctx.foldl_apps(motive, shifted_indices.into_iter().rev());
            let c_app = self.ctx.mk_app(c_app, c_app0);

            let minor_type = self.mk_pis_dep(v.as_slice(), 0, c_app);
            let minor_type = self.mk_pis_dep(all_ctor_args.as_slice(), 0, minor_type);
            let minor_name = match self.ctx.read_name(ctor.name) {
                // Use the constructor's name if it's available;
                crate::name::Name::Str(_, sfx, _) => self.ctx.str(self.ctx.anonymous(), sfx),
                // If the constructor name isn't available for some reason, use a generic one
                _ => {
                    let minor_name = self.ctx.str1("m");
                    self.ctx.append_index_after(minor_name, ctor_idx as u64)
                }
            };
            out.push((minor_name, BinderStyle::Default, minor_type));
        }
        out
    }

    fn mk_minors(&mut self, st: &mut InductiveCheckState<'t>) {
        assert_eq!(st.all_inductives_incl_specialized.len(), st.ind_consts.len());
        for ind_ty in st.all_inductives_incl_specialized.iter() {
            st.minors.push(self.mk_minors1group(st, ind_ty.ctors.as_slice()))
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
        let num_minors = u16::try_from(st.minors.iter().map(|g| g.len()).sum::<usize>()).expect("too many minors");
        let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
        for (pos, dom_v) in rec_args.iter().copied() {
            self.tc_cache.clear();
            let (u_i_ty, xs, u_i_v, u_i_depth) = self.handle_rec_args_aux(dom_v, base_depth);
            let (it_idx, applied_indices) = self.get_i_indices_at(st, u_i_ty, u_i_v, u_i_depth);
            let it_name = st.all_inductives_incl_specialized.get(it_idx).map(|x| x.name).unwrap();
            let rec_name = self.ctx.str(it_name, rec_str_ptr);
            let rec_app = self.ctx.mk_const(rec_name, st.rec_uparams.unwrap());
            let n = u16::try_from(xs.len()).expect("telescope exceeds u16");
            let total = u16::try_from(u_i_depth).expect("depth exceeds u16");
            let param_vars = self.param_vars(st, total - st.num_params());
            let motive_vars: Vec<ExprPtr<'t>> =
                (0..st.num_motives()).map(|j| self.ctx.mk_var(total - 1 - (st.num_params() + j))).collect();
            let minor_vars: Vec<ExprPtr<'t>> =
                (0..num_minors).map(|k| self.ctx.mk_var(total - 1 - (st.minor_base() + k))).collect();
            let app = self.ctx.foldl_apps(rec_app, param_vars.into_iter());
            let app = self.ctx.foldl_apps(app, motive_vars.into_iter());
            let app = self.ctx.foldl_apps(app, minor_vars.into_iter());
            let app = self.ctx.foldl_apps(app, applied_indices.iter().copied().rev());
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
        flat_mapped_minors: &[Bndr<'t>],
        minor_idx: u16,
    ) -> RecRule<'t> {
        let num_minors = u16::try_from(flat_mapped_minors.len()).expect("too many minors");
        let ctor_args_base = u32::from(st.minor_base() + num_minors);
        let (_, _, args_depth, all_ctor_args, rec_ctor_args) =
            self.sep_nonrec_rec_ctor_args(st, ctor.ty, ctor_args_base);
        let handled_rec_args =
            self.handle_rec_ctor_args_rec_rule(st, rec_ctor_args.as_slice(), ctor_args_base, args_depth);
        let n_args = u16::try_from(all_ctor_args.len()).expect("telescope exceeds u16");
        let total = u16::try_from(args_depth).expect("depth exceeds u16");
        let arg_vars: Vec<ExprPtr<'t>> = (0..n_args).map(|j| self.ctx.mk_var(n_args - 1 - j)).collect();
        let this_minor = self.ctx.mk_var(total - 1 - (st.minor_base() + minor_idx));
        let comp_rhs = self.ctx.foldl_apps(this_minor, arg_vars.iter().copied());
        let comp_rhs = self.ctx.foldl_apps(comp_rhs, handled_rec_args.iter().copied());
        let comp_rhs = self.mk_lambdas_dep(all_ctor_args.as_slice(), 0, comp_rhs);
        let comp_rhs = self.mk_lambdas_flat(flat_mapped_minors, comp_rhs);
        let motives = st.motives.clone();
        let comp_rhs = self.mk_lambdas_flat(motives.as_slice(), comp_rhs);
        let params = st.local_params.clone();
        let comp_rhs = self.mk_lambdas_dep(params.as_slice(), 0, comp_rhs);
        let num_fields = self.ctx.pi_telescope_size(ctor.ty) as usize - st.local_params.len();
        RecRule {
            ctor_name: ctor.name,
            ctor_telescope_size_wo_params: u16::try_from(num_fields).unwrap(),
            val: comp_rhs,
        }
    }

    fn mk_rec_rules(&mut self, st: &InductiveCheckState<'t>) -> Vec<Vec<RecRule<'t>>> {
        let mut rec_rules = Vec::new();
        let minors = st.flat_minors();
        let mut overall_ctor_idx = 0u16;
        for ind_ty in st.all_inductives_incl_specialized.iter() {
            let mut grp = Vec::new();
            for ctor in ind_ty.ctors.iter().copied() {
                let rec_rule = self.mk_rec_rule1(st, ctor, minors.as_slice(), overall_ctor_idx);
                overall_ctor_idx += 1;
                grp.push(rec_rule);
            }
            rec_rules.push(grp);
        }
        rec_rules
    }

    // Assert that the inductive types being added to the extension which
    // are also in the export file are definitionally equal.
    fn assert_nonnested_tys_def_eq(&mut self, base_ind: &InductiveData<'t>, st: &InductiveCheckState<'t>) {
        assert!(!st.is_nested());
        for name in base_ind.all_ind_names.iter() {
            match (self.env.get_old_declar(name), self.env.get_temp_declar(name)) {
                (Some(Declar::Inductive(old)), Some(Declar::Inductive(new))) => {
                    assert!(old.aux_data_ck(new));
                    debug_assert!(!std::ptr::eq(old, new));
                    self.tc_cache.clear();
                    self.assert_def_eq(old.info.ty, new.info.ty);
                }
                _ => panic!(),
            }
        }
    }

    fn assert_nonnested_ctors_def_eq(&mut self, st: &InductiveCheckState<'t>) {
        assert!(!st.is_nested());
        for inductive in st.all_inductives_incl_specialized.iter() {
            for ctor in inductive.ctors.iter() {
                match (self.env.get_old_declar(&ctor.name), self.env.get_temp_declar(&ctor.name)) {
                    (Some(Declar::Constructor(old)), Some(Declar::Constructor(new))) => {
                        assert!(old.aux_data_ck(new));
                        debug_assert!(!std::ptr::eq(old, new));
                        self.tc_cache.clear();
                        self.assert_def_eq(old.info.ty, new.info.ty);
                    }
                    _ => panic!(),
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
        assert_eq!(imported_rr.ctor_name, constructed_rr.ctor_name);
        assert_eq!(imported_rr.ctor_telescope_size_wo_params, constructed_rr.ctor_telescope_size_wo_params);
        let rr_made_val = self.ctx.subst_expr_levels(constructed_rr.val, st.rec_uparams.unwrap(), old);
        self.assert_def_eq(imported_rr.val, rr_made_val);
    }

    fn assert_nonnested_recursors_def_eq(&mut self, st: &InductiveCheckState<'t>, recursors: &Vec<Declar<'t>>) {
        assert!(!st.is_nested());
        for new_rec in recursors {
            match (self.env.get_old_declar(&new_rec.info().name), new_rec) {
                (
                    Some(old @ Declar::Recursor(old_r @ RecursorData { rec_rules: old_rec_rules, .. })),
                    new @ Declar::Recursor(new_r @ RecursorData { rec_rules: new_rec_rules, .. })
                ) => {
                    self.tc_cache.clear();
                    assert!(old_r.aux_data_ck(new_r));
                    assert!(!std::ptr::eq(old, new));
                    // Should be structurally != because they come from different envs.
                    assert_ne!(old, new);
                    let imported_w_new_uparams = self.ctx.subst_expr_levels(old.info().ty, old.info().uparams, st.rec_uparams.unwrap());
                    self.assert_def_eq(imported_w_new_uparams, new.info().ty);
                    assert_eq!(old_rec_rules.len(), new_rec_rules.len());
                    for (r_old, r_new) in old_rec_rules.iter().zip(new_rec_rules.iter()) {
                        self.assert_nonnested_rec_rule_def_eq(st, old.info().uparams, r_old, r_new)
                    }
                }
                _ => panic!("Expected (Declar::Recursor, Declar::Recursor)"),
            };
        }
    }

    fn mk_recursor_aux(
        &mut self,
        st: &InductiveCheckState<'t>,
        ind_name: NamePtr<'t>,
        motive_idx: u16,
        major: Bndr<'t>,
        local_indices: &[Bndr<'t>],
        flat_mapped_minors: &[Bndr<'t>],
        rec_rules: &[RecRule<'t>],
    ) -> Declar<'t> {
        let num_indices = u16::try_from(local_indices.len()).expect("index count exceeds u16");
        let num_minors = u16::try_from(flat_mapped_minors.len()).expect("too many minors");
        let gap = st.num_motives() + num_minors;
        let total = st.minor_base() + num_minors + num_indices + 1;

        let motive = self.ctx.mk_var(total - 1 - (st.num_params() + motive_idx));
        let index_vars: Vec<ExprPtr<'t>> =
            (0..num_indices).map(|k| self.ctx.mk_var(total - 1 - (st.minor_base() + num_minors + k))).collect();
        let major_var = self.ctx.mk_var(0);
        let motive_app_base = self.ctx.foldl_apps(motive, index_vars.into_iter());
        let motive_app = self.ctx.mk_app(motive_app_base, major_var);

        let major_ty = self.ctx.lift(major.2, num_indices, gap);
        let rec_ty = self.ctx.mk_pi(major.0, major.1, major_ty, motive_app);
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
            all_inductives: Arc::from(st.all_inductives_incl_specialized.iter().map(|x| x.name).collect::<Vec<_>>()),
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
        let main_ind_ty_name = base_mutuals.get(0).map(|zth| zth.name).unwrap();
        let mut specialized_rec_names_to_unspecialized_rec_names = crate::util::new_fx_index_map();
        let rec_str = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));

        // The MODIFIED version looked up in the new environment. The modification would
        // just be additions to `all_ind_names`, which now contains the `_nested.Array`
        // specialized type names.
        let InductiveData { all_ind_names, .. } = self.env.get_inductive(&main_ind_ty_name).unwrap();
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
            specialized_rec_names_to_unspecialized_rec_names.insert(specialized_rec_name, unspecialized_rec_name);
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
        let ConstructorData { inductive_name, .. } = self.env.get_constructor(&c)?;
        let unspecialized_ty = st.nested_to_unspecialized_ty.get(inductive_name).copied()?;
        Some((unspecialized_ty, *inductive_name))
    }

    /// If `c` is `_nested_Array_1.mk`, return just `Array.mk`,
    ///
    /// This is only used in restoring recursor rules, since those hold the constructor name.
    fn restore_ctor_name(&mut self, st: &InductiveCheckState<'t>, ctor_name: NamePtr<'t>) -> NamePtr<'t> {
        // from `_nested_Array_1.mk`, retrieve `(Array Lean.Syntax, _nested.Array_1)`
        let (unspecialized_ty, base_ind_name) = self.get_nested_if_aux_ctor(st, ctor_name).unwrap();
        // Now get just `Const(Array, [])`
        let unspecialized_f = self.ctx.unfold_apps_fun(unspecialized_ty);
        // Get just the name for `Array`
        let (unspecialized_ty_name, ..) = self.ctx.try_const_info(unspecialized_f).unwrap();
        // Replace ctor_name[specialized_name |-> unspecialized_name]
        // e.g. `_nested.Array_1.mk |-> Array.mk`
        self.ctx.replace_pfx(ctor_name, base_ind_name, unspecialized_ty_name)
    }

    fn restore_replace(
        &mut self,
        e: ExprPtr<'t>,
        num_params: usize,
        depth: u16,
        st: &InductiveCheckState<'t>,
        specialized_rec_names_to_unspecialized_rec_names: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
    ) -> ExprPtr<'t> {
        match self.replace_f(e, num_params, depth, st, specialized_rec_names_to_unspecialized_rec_names) {
            Some(out) => out,
            None => match self.ctx.read_expr(e) {
                Var { .. } | Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => e,
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        num_params,
                        depth,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let body =
                        self.restore_replace(body, num_params, depth + 1, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        num_params,
                        depth,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let body =
                        self.restore_replace(body, num_params, depth + 1, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Let { data: &crate::expr::LetData { binder_name, binder_type, val, body, nondep }, .. } => {
                    let binder_type = self.restore_replace(
                        binder_type,
                        num_params,
                        depth,
                        st,
                        specialized_rec_names_to_unspecialized_rec_names,
                    );
                    let val =
                        self.restore_replace(val, num_params, depth, st, specialized_rec_names_to_unspecialized_rec_names);
                    let body =
                        self.restore_replace(body, num_params, depth + 1, st, specialized_rec_names_to_unspecialized_rec_names);
                    self.ctx.mk_let(binder_name, binder_type, val, body, nondep)
                }
                Proj { ty_name, idx, structure, .. } => {
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
                    let fun =
                        self.restore_replace(fun, num_params, depth, st, specialized_rec_names_to_unspecialized_rec_names);
                    let arg =
                        self.restore_replace(arg, num_params, depth, st, specialized_rec_names_to_unspecialized_rec_names);
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
    /// (_nested.Array_1.rec, Lean.Syntax.rec_1)\
    /// (_nested.List_2.rec, Lean.Syntax.rec_2)
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
        if let Const { name, levels, .. } = self.ctx.read_expr(e) {
            // If e was `Const(_nested.Array_1.rec)`, return `Const(Lean.Syntax.rec_1)`
            if let Some(rec_name) = specialized_rec_names_to_unspecialized_rec_names.get(&name) {
                return Some(self.ctx.mk_const(*rec_name, levels))
            }
        }
        let (_, c_name, _, e_args) = self.ctx.unfold_const_apps(self.arena, e)?;
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
            let outer = self.ctx.foldl_apps(inner, e_args.iter().copied().skip(st.num_params as usize));
            return Some(outer)
        }
        let (nested_no_inst, aux_i_name) = self.get_nested_if_aux_ctor(st, c_name)?;

        debug_assert!(e_args.len() >= st.num_params as usize);
        let nested_inst = self.inst_params_at(nested_no_inst, num_params, depth);
        let (nested_f, i_args) = self.ctx.unfold_apps(self.arena, nested_inst);
        // Replace one of the nested constructor applications with a regular ctor application.
        //
        // replacing(3) c := _nested.Array_3.mk, auxI_name := _nested.Array_3, I_c := Array, c' := Array.mk.{0}
        // replacing(3) c := _nested.List_4.nil, auxI_name := _nested.List_4, I_c := List, c' := List.nil.{0}
        match self.ctx.read_expr(nested_f) {
            Const { name: i_name, levels, .. } => {
                let cprime_name = self.ctx.replace_pfx(c_name, aux_i_name, i_name);
                let cprime = self.ctx.mk_const(cprime_name, levels);
                let inner = self.ctx.foldl_apps(cprime, i_args.iter().copied());
                let outer = self.ctx.foldl_apps(inner, e_args.iter().copied().skip(st.num_params as usize));
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
        let is_pi = matches!(self.ctx.read_expr(e), Pi { .. });
        let num_params = st.local_params.len();
        let mut cur = self.value_of(e);
        let mut binders: Vec<(NamePtr<'t>, BinderStyle, ExprPtr<'t>)> = Vec::with_capacity(num_params);
        for level in 0..num_params {
            let depth = u32::try_from(level).expect("parameter count exceeds u32");
            let f = self.force_thunk(depth, cur);
            let (binder_name, binder_style, dom) = match f {
                Value::Pi { binder_name, binder_style, domain, .. } => (*binder_name, *binder_style, *domain),
                // Also match on Lambda for restoring recursor rules.
                Value::Lam { binder_name, binder_style, .. } => {
                    let d = self.lam_domain(depth, f);
                    (*binder_name, *binder_style, d)
                }
                _ => panic!("malformed recursor"),
            };
            let dom_e = self.quote(depth, dom);
            let fresh = self.mk_bvar_hc(depth, dom);
            cur = match f {
                Value::Pi { body, .. } => self.apply_closure(depth + 1, body, fresh, Some(dom)),
                Value::Lam { body, .. } => self.apply_closure(depth + 1, body, fresh, None),
                _ => unreachable!(),
            };
            binders.push((binder_name, binder_style, dom_e));
        }
        let body_depth = u32::try_from(num_params).expect("parameter count exceeds u32");
        let body = self.quote(body_depth, cur);
        let mut out = self.restore_replace(body, num_params, 0, st, nested_rec_name_to_rec_name);
        while let Some((binder_name, binder_style, dom_e)) = binders.pop() {
            out = if is_pi {
                self.ctx.mk_pi(binder_name, binder_style, dom_e, out)
            } else {
                self.ctx.mk_lambda(binder_name, binder_style, dom_e, out)
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
        let resolved_rec_name =
            specialized_rec_names_to_unspecialized_rec_names.get(&rec_name).copied().unwrap_or(rec_name);
        // The new environment's recursor for this type; e.g. the recursor
        // that's in the environment for _nested.Array_1.rec
        let new_env_rec @ RecursorData { .. } = self.env.get_recursor(&rec_name).cloned().unwrap();
        let restored_ty = self.restore_e(st, new_env_rec.info.ty, specialized_rec_names_to_unspecialized_rec_names);
        let mut rules = Vec::new();
        for rule in new_env_rec.rec_rules.iter().copied() {
            let val = self.restore_e(st, rule.val, specialized_rec_names_to_unspecialized_rec_names);
            let ctor_name =
                if rec_name == resolved_rec_name { rule.ctor_name } else { self.restore_ctor_name(st, rule.ctor_name) };
            rules.push(RecRule { ctor_name, val, ..rule })
        }
        RecursorData {
            info: DeclarInfo { name: resolved_rec_name, ty: restored_ty, ..new_env_rec.info },
            all_inductives: all_ind_names_no_specialized.clone(),
            rec_rules: Arc::from(rules),
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
        let restored = self.restore_recursor1(st, ind_names_no_specialized, nested_rec_name_to_rec_name, rec_name);
        let resolved_rec_name = nested_rec_name_to_rec_name.get(&rec_name).copied().unwrap_or(rec_name);
        match self.env.get_old_declar(&resolved_rec_name) {
            Some(Declar::Recursor(original @ RecursorData { .. })) => {
                assert!(original.aux_data_ck(&restored));
                self.tc_cache.clear();
                self.assert_def_eq(original.info.ty, restored.info.ty);
                // have to do the rec rules as well.
                assert_eq!(original.rec_rules.len(), restored.rec_rules.len());
                for i in 0..original.rec_rules.len() {
                    let old = original.rec_rules[i];
                    let new = restored.rec_rules[i];
                    assert_eq!(old.ctor_name, new.ctor_name);
                    self.tc_cache.clear();
                    self.assert_def_eq(old.val, new.val);
                }
            }
            _ => {}
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
            self.check_restored_recursor1(st, ind_names_no_specialized, specialized_rec_name_to_rec_name, rec_name)
        }

        // Check the recursors constructed for the specialized types,
        // like `_nested.Array_1.rec` after restoring it to `Lean.Syntax.rec_1`
        for specialized_ty_rec_name in specialized_rec_name_to_rec_name.keys().copied() {
            self.check_restored_recursor1(
                st,
                ind_names_no_specialized,
                specialized_rec_name_to_rec_name,
                specialized_ty_rec_name,
            )
        }
    }

    fn check_restored_ctor1(
        &mut self,
        st: &InductiveCheckState<'t>,
        rec_name_map: &FxIndexMap<NamePtr<'t>, NamePtr<'t>>,
        old_ctor: &ConstructorData<'t>,
    ) {
        let new_ctor @ ConstructorData { .. } = self.env.get_constructor(&old_ctor.info.name).unwrap();
        assert!(old_ctor.aux_data_ck(new_ctor));
        let new_ty = self.restore_e(st, new_ctor.info.ty, rec_name_map);
        self.tc_cache.clear();
        self.assert_def_eq(old_ctor.info.ty, new_ty);
    }

    fn restore_and_check(
        &mut self,
        st: &InductiveCheckState<'t>,
        unmodified_mutuals: &Vec<IndTyHeader<'t>>,
        ind_names_no_specialized: &Arc<[NamePtr<'t>]>,
    ) {
        let specialized_to_unspecialized_rec_names = self.mk_specialized_rec_to_unspecialized_map(unmodified_mutuals);
        for unmodified_ind_type in unmodified_mutuals.iter() {
            match (
                self.env.get_old_declar(&unmodified_ind_type.name),
                self.env.get_temp_declar(&unmodified_ind_type.name),
            ) {
                (Some(Declar::Inductive(old)), Some(Declar::Inductive(new))) => {
                    assert!(old.aux_data_ck(new));
                    debug_assert!(!std::ptr::eq(old, new));
                    self.tc_cache.clear();
                    self.assert_def_eq(old.info.ty, new.info.ty);
                }
                _ => panic!(),
            }

            for ctor in unmodified_ind_type.ctors.iter() {
                let ctor = match self.env.get_old_declar(&ctor.name) {
                    Some(Declar::Constructor(c)) => c.clone(),
                    _ => panic!(),
                };
                self.check_restored_ctor1(st, &specialized_to_unspecialized_rec_names, &ctor);
            }
        }
        self.restore_recursors(st, &specialized_to_unspecialized_rec_names, ind_names_no_specialized);
    }
}
