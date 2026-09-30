// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::tc::TypeChecker;
use crate::checker::value::{S, Value};
use crate::term::ptr::{LevelPtr, LevelsPtr, NamePtr};

pub(crate) const MAX_TRACKED: u32 = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Sig {
    pub(crate) arity: u8,
    pub(crate) prop_arg: u64,
    pub(crate) arg_known: u64,
    pub(crate) absent_arg: u64,
    pub(crate) prop_result: u64,
    pub(crate) result_known: u64,
}

impl Sig {
    pub(crate) const ALL_RELEVANT: Sig = Sig {
        arity: 0,
        prop_arg: 0,
        arg_known: 0,
        absent_arg: 0,
        prop_result: 0,
        result_known: 0,
    };

    #[inline]
    fn ignorable(&self) -> u64 {
        (self.prop_arg & self.arg_known) | self.absent_arg
    }

    #[inline]
    pub(crate) fn masks_any_arg(&self) -> bool {
        self.ignorable() != 0
    }

    #[inline]
    pub(crate) fn arg_is_ignorable(&self, idx: u32) -> bool {
        idx < MAX_TRACKED && (self.ignorable() >> idx) & 1 == 1
    }

    #[inline]
    pub(crate) fn result_is_not_proof(&self, k: u32) -> bool {
        k < MAX_TRACKED && (self.result_known >> k) & 1 == 1 && (self.prop_result >> k) & 1 == 0
    }
}

pub(crate) fn app_prefix_len(spine: S<'_>) -> u32 {
    if !spine.has_proj() {
        return spine.len();
    }
    let len = spine.len();
    spine
        .elims_rev()
        .zip((0..len).rev())
        .filter(|(elim, _)| !elim.is_app())
        .last()
        .map_or(len, |(_, i)| i)
}

impl<'t> TypeChecker<'_, 't, '_> {
    pub(crate) fn sig_of(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> Sig {
        if self.env.has_temp_ext() {
            return Sig::ALL_RELEVANT;
        }
        if let Some(s) = self.ctx.sig_cache.get(&(name, levels)) {
            return *s;
        }
        if !self.ctx.sig_computing.insert((name, levels)) {
            return Sig::ALL_RELEVANT;
        }
        let s = self.sig_compute(name, levels);
        self.ctx.sig_computing.remove(&(name, levels));
        self.ctx.sig_cache.insert((name, levels), s);
        s
    }

    fn sig_compute(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> Sig {
        let mut dom: Vec<Option<LevelPtr<'t>>> = Vec::new();
        let mut cur = self.const_head_type(name, levels);
        let mut depth = 0u32;
        let terminal = loop {
            let cur_f = self.force_all(depth, cur);
            let Value::Pi { domain, body, .. } = cur_f else {
                break Some(cur_f);
            };
            if dom.len() >= MAX_TRACKED as usize {
                break None;
            }
            let d = *domain;
            dom.push(self.level_of_type(depth, d));
            let fresh = self.mk_bvar_hc(depth, d);
            cur = self.apply_closure(depth + 1, body, fresh, Some(d));
            depth += 1;
        };

        let n = dom.len();
        let mut prop_arg = 0u64;
        let mut arg_known = 0u64;
        for (i, l) in dom.iter().enumerate() {
            if let Some(l) = *l {
                arg_known |= 1u64 << i;
                if self.ctx.is_zero(l) {
                    prop_arg |= 1u64 << i;
                }
            }
        }

        let mut prop_result = 0u64;
        let mut result_known = 0u64;
        if let Some(term) = terminal
            && let Some(sb) = self.level_of_type(depth, term)
        {
            let mut r = sb;
            if n < MAX_TRACKED as usize {
                result_known |= 1u64 << n;
                if self.ctx.is_zero(r) {
                    prop_result |= 1u64 << n;
                }
            }
            for k in (0..n).rev() {
                let Some(s) = dom[k] else { break };
                let im = self.ctx.imax(s, r);
                r = self.ctx.simplify(im);
                result_known |= 1u64 << k;
                if self.ctx.is_zero(r) {
                    prop_result |= 1u64 << k;
                }
            }
        }

        Sig {
            arity: u8::try_from(n).expect("telescope arity exceeds the tracked bound"),
            prop_arg,
            arg_known,
            absent_arg: self.absent_args(name),
            prop_result,
            result_known,
        }
    }

    fn absent_args(&mut self, name: NamePtr<'t>) -> u64 {
        let Some((_, val)) = self.env.get_declar_val(name) else {
            return 0;
        };
        let Some(decl) = self.env.get_declar(name) else {
            return 0;
        };
        let ty = decl.info().ty;
        let mut body = val;
        let mut arity = 0u32;
        while let crate::term::expr::Expr::Lambda { body: inner, .. } = *body {
            if arity == MAX_TRACKED {
                break;
            }
            body = inner;
            arity += 1;
        }
        if arity == 0 || u32::from(body.num_loose_bvars()) > MAX_TRACKED {
            return 0;
        }
        let used = body.as_ref().fv_mask();
        let mut absent = 0u64;
        let mut rest_ty = ty;
        for i in 0..arity {
            let crate::term::expr::Expr::Pi { body: rest, .. } = *rest_ty else {
                break;
            };
            let unused_in_value = (used >> (arity - 1 - i)) & 1 == 0;
            if unused_in_value && crate::term::expr::ignores_binder(rest) {
                absent |= 1u64 << i;
            }
            rest_ty = rest;
        }
        absent
    }
}
