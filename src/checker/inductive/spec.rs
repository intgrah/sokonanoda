use super::{IndTyHeader, InductiveCheckState};
use crate::checker::tc::TypeChecker;
use crate::checker::value::Value;
use crate::outcome::{ensure, ensure_eq, reject};
use crate::term::ptr::{ExprPtr, LevelsPtr, NamePtr};

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    /// Check the 0th element of the list of inductive types; this one is different
    /// than the mutuals, because we need to determine the target for the block codom
    /// and some other stuff.
    fn check_inductive_spec_0th(
        &mut self,
        uparams: LevelsPtr<'t>,
        st: &mut InductiveCheckState<'t>,
    ) {
        self.tc_cache.clear();
        let (ind_name, ind_ty) = st
            .all_inductives_incl_specialized
            .first()
            .map(|x| (x.name, x.ty))
            .unwrap();
        let mut depth = 0u32;
        let mut env = self.empty_env();
        let mut cur = self.value_of(ind_ty);
        let mut indices = Vec::new();
        let mut i = 0;
        while let Some(Value::Pi { domain, body, .. }) = self.force_pi(depth, cur) {
            let domain = *domain;
            if i < st.local_params.len() {
                let stored = st.local_params[i];
                self.tc_cache.clear();
                let expected = self.eval(depth, env, stored);
                ensure!(self.def_eq_at(depth, domain, expected), "def_eq failed");
            } else {
                let binder_type = self.quote(depth, domain);
                indices.push(binder_type);
            }
            let fresh = self.mk_bvar_hc(depth, domain);
            env = self.env_extend(env, fresh);
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
    fn check_inductive_specs_mutual1(
        &mut self,
        st: &mut InductiveCheckState<'t>,
        name: NamePtr<'t>,
        ty: ExprPtr<'t>,
    ) {
        self.tc_cache.clear();
        let mut depth = 0u32;
        let mut cur = self.value_of(ty);
        let mut indices = Vec::new();
        let mut i = 0;
        while let Some(Value::Pi { domain, body, .. }) = self.force_pi(depth, cur) {
            let domain = *domain;
            if i >= st.local_params.len() {
                let binder_type = self.quote(depth, domain);
                indices.push(binder_type);
            }
            let fresh = self.mk_bvar_hc(depth, domain);
            cur = self.apply_closure(depth + 1, body, fresh, Some(domain));
            depth += 1;
            i += 1;
        }
        let codom_level = self.ensure_sort_v(depth, cur);
        ensure!(self.ctx.eq_antisymm(codom_level, st.block_codom.unwrap()));
        st.local_indices.push(indices);
        st.ind_consts.push(self.ctx.mk_const(name, st.uparams));
    }
    /// This starts by receiving the "full" `InductiveType` specification from the export
    /// file for the actual declaration being checked. It *ALSO* gets the `NestedInductiveState`,
    /// since the process of checking these also has to deal with the new types created
    /// during the nest procedure.
    pub(super) fn check_inductive_specs(&mut self, st: &mut InductiveCheckState<'t>) {
        let nbefore = st.all_inductives_incl_specialized.len();
        for i in 0..st.all_inductives_incl_specialized.len() {
            if i == 0 {
                self.check_inductive_spec_0th(st.uparams, st);
                assert_eq!(st.local_indices.len(), 1);
            } else {
                assert_eq!(st.local_indices.len(), i);
                let IndTyHeader { name, ty, .. } = st.all_inductives_incl_specialized[i];
                self.check_inductive_specs_mutual1(st, name, ty);
            }
        }
        assert_eq!(st.all_inductives_incl_specialized.len(), nbefore);
        assert_eq!(
            st.all_inductives_incl_specialized.len(),
            st.local_indices.len()
        );
    }
    pub(super) fn check_declared_metadata(
        &mut self,
        st: &InductiveCheckState<'t>,
        unmodified: &[IndTyHeader<'t>],
    ) {
        let num_params = usize::from(st.num_params());
        for (i, header) in unmodified.iter().enumerate() {
            let ind = self
                .env
                .get_inductive(header.name)
                .expect("inductive is not declared");
            ensure_eq!(
                usize::from(ind.num_params),
                num_params,
                "inductive declares the wrong number of parameters"
            );
            ensure_eq!(
                usize::from(ind.num_indices),
                st.local_indices[i].len(),
                "inductive declares the wrong number of indices"
            );
            ensure_eq!(
                ind.all_ctor_names.len(),
                header.ctors.len(),
                "inductive declares the wrong number of constructors"
            );
            for (ctor_idx, ctor) in header.ctors.iter().enumerate() {
                let telescope = ctor.ty.pi_telescope_size() as usize;
                ensure!(
                    telescope >= num_params,
                    "constructor telescope is shorter than the parameters"
                );
                let cd = self
                    .env
                    .get_constructor(ctor.name)
                    .expect("constructor is not declared");
                ensure_eq!(
                    cd.inductive_name,
                    header.name,
                    "constructor declares the wrong inductive"
                );
                ensure_eq!(
                    usize::from(cd.ctor_idx),
                    ctor_idx,
                    "constructor declares the wrong index"
                );
                ensure_eq!(
                    usize::from(cd.num_params),
                    num_params,
                    "constructor declares the wrong number of parameters"
                );
                ensure_eq!(
                    usize::from(cd.num_fields),
                    telescope - num_params,
                    "constructor declares the wrong number of fields"
                );
            }
            let rec_name = {
                let rec_str_ptr = self.ctx.alloc_string(std::borrow::Cow::Borrowed("rec"));
                self.ctx.str(header.name, rec_str_ptr)
            };
            if let Some(rd) = self.env.get_recursor(rec_name) {
                ensure_eq!(
                    rd.is_k,
                    st.k_target.unwrap(),
                    "recursor declares the wrong k-reduction flag"
                );
                ensure_eq!(
                    usize::from(rd.num_params),
                    num_params,
                    "recursor declares the wrong number of parameters"
                );
                ensure_eq!(
                    usize::from(rd.num_indices),
                    st.local_indices[i].len(),
                    "recursor declares the wrong number of indices"
                );
            }
        }
    }
    fn large_elim_test_aux(
        &mut self,
        ctor_type_cursor: ExprPtr<'t>,
        mut rem_params: usize,
    ) -> bool {
        self.tc_cache.clear();
        let mut depth = 0u32;
        let mut cur = self.value_of(ctor_type_cursor);
        let mut non_prop_levels: Vec<u32> = Vec::new();
        while let Value::Pi { domain, body, .. } = cur {
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

        let non_prop_ctor_telescope_elems: Vec<ExprPtr<'t>> = non_prop_levels
            .iter()
            .map(|l| {
                self.ctx
                    .mk_var(u16::try_from(depth - 1 - l).expect("depth exceeds u16"))
            })
            .collect();
        let end_of_telescope = self.quote(depth, cur);
        let (_, ind_ty_params_and_indices) = end_of_telescope.unfold_apps(self.arena);

        // Check whether `non_prop_ctor_telescope_elems` is a subset of
        // `ind_ty params ++ ind_ty indices`
        //
        // if the list of non-prop constructor args is NOT a subset of
        // the exprs being applied to the inductive (which is params + indices)
        // then we can say that this type only eliminates into Prop/Sort 0
        non_prop_ctor_telescope_elems
            .iter()
            .all(|arg| ind_ty_params_and_indices.contains(arg))
    }
    fn large_elim_test(&mut self, st: &InductiveCheckState<'t>) -> bool {
        if st.is_nonzero.unwrap() {
            // If our inductive is in `Type <n>`, it's large eliminating
            return true;
        }

        match st.all_inductives_incl_specialized.as_slice() {
            [] => reject!("inductive declaration with no types declared"),
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
        if !st.uparams.contains_param(p) {
            return p;
        }
        // Lean's pretty printer starts at 1 for universes.
        let mut i = 1u64;
        loop {
            let candidate = self.ctx.append_index_after(p, i);
            if st.uparams.contains_param(candidate) {
                i += 1;
            } else {
                return candidate;
            }
        }
    }
    pub(super) fn mk_elim_level(&mut self, st: &mut InductiveCheckState<'t>) {
        if self.large_elim_test(st) {
            let elim_level = self.gen_elim_level(st);
            let elim_level = self.ctx.param(elim_level);
            // Extra work since you want the new thing at the front of the vector (in position 0)
            let rec_levels = {
                let mut base = vec![elim_level];
                for l in st.uparams.as_ref().iter().copied() {
                    base.push(l);
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
        }
    }
}
