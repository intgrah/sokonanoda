// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::tc::TypeChecker;
use crate::checker::value::{S, Value};
use crate::term::level::Level;
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

#[derive(Debug, Clone, Copy)]
pub(crate) struct SigTemplate<'t> {
    uparams: LevelsPtr<'t>,
    dom: &'t [Option<LevelPtr<'t>>],
    result: Option<LevelPtr<'t>>,
    arg_known: u64,
    absent_arg: u64,
    result_span: u64,
}

fn zero_under<'t>(level: LevelPtr<'t>, params: &[LevelPtr<'t>], args: &[LevelPtr<'t>]) -> bool {
    match *level {
        Level::Zero => true,
        Level::Succ(..) => false,
        Level::Param(..) => params
            .iter()
            .position(|p| *p == level)
            .is_some_and(|i| args[i].is_always_zero()),
        Level::Max(l, r, ..) => zero_under(l, params, args) && zero_under(r, params, args),
        Level::IMax(_, r, ..) => zero_under(r, params, args),
    }
}

impl<'t> SigTemplate<'t> {
    fn at(&self, levels: LevelsPtr<'t>) -> Sig {
        let params = self.uparams.as_ref();
        let args = levels.as_ref();
        let mut prop_arg = 0u64;
        for (i, l) in self.dom.iter().enumerate() {
            if let Some(l) = *l
                && zero_under(l, params, args)
            {
                prop_arg |= 1u64 << i;
            }
        }
        let prop_result = match self.result {
            Some(l) if zero_under(l, params, args) => self.result_span,
            _ => 0,
        };
        Sig {
            arity: u8::try_from(self.dom.len()).expect("telescope arity exceeds the tracked bound"),
            prop_arg,
            arg_known: self.arg_known,
            absent_arg: self.absent_arg,
            prop_result,
            result_known: self.result_span,
        }
    }
}

impl<'t> TypeChecker<'_, 't, '_> {
    pub(crate) fn sig_of(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> Sig {
        if self.env.has_temp_ext() {
            return Sig::ALL_RELEVANT;
        }
        if let Some(s) = self.ctx.sig_cache.get(&(name, levels)) {
            return *s;
        }
        let template = if let Some(t) = self.ctx.sig_templates.get(&name) {
            *t
        } else {
            if !self.ctx.sig_computing.insert(name) {
                return Sig::ALL_RELEVANT;
            }
            let t = self.sig_template(name);
            self.ctx.sig_computing.remove(&name);
            self.ctx.sig_templates.insert(name, t);
            t
        };
        crate::outcome::ensure!(
            template.uparams.len() == levels.len(),
            "wrong number of universe levels for {name:?}"
        );
        let s = template.at(levels);
        self.ctx.sig_cache.insert((name, levels), s);
        s
    }

    fn sig_template(&mut self, name: NamePtr<'t>) -> SigTemplate<'t> {
        let Some(d) = self.env.get_declar(name) else {
            crate::outcome::reject!("sig_template: unknown const {name:?}")
        };
        let uparams = d.info().uparams;
        let mut dom: Vec<Option<LevelPtr<'t>>> = Vec::new();
        let mut cur = self.const_head_type(name, uparams);
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
        let arg_known = dom
            .iter()
            .enumerate()
            .filter(|(_, l)| l.is_some())
            .fold(0u64, |m, (i, _)| m | (1u64 << i));

        let result = terminal.and_then(|term| self.level_of_type(depth, term));
        let result_span = if result.is_some() {
            let known_from = dom.iter().rposition(Option::is_none).map_or(0, |k| k + 1);
            let below = u32::try_from(known_from)
                .ok()
                .and_then(|k| 1u64.checked_shl(k))
                .map_or(u64::MAX, |bit| bit - 1);
            let upto = n.min(MAX_TRACKED as usize - 1);
            (u64::MAX >> (63 - upto)) & !below
        } else {
            0
        };

        SigTemplate {
            uparams,
            dom: self.ctx.arena.alloc_slice_copy(&dom),
            result,
            arg_known,
            absent_arg: self.absent_args(name),
            result_span,
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
