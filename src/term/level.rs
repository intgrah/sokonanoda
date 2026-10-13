// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

//! Implementation of the `Level` type representing universes
use crate::checker::context::TcCtx;
use crate::term::id::{LevelId, LevelsId, NameId, ZERO};
use Level::{IMax, Max, Param, Succ, Zero};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(NameId),
}

impl TcCtx<'_> {
    fn combining(&mut self, l: LevelId, r: LevelId) -> LevelId {
        match (self.level(l), self.level(r)) {
            (Zero, _) => r,
            (_, Zero) => l,
            (Succ(l), Succ(r)) => {
                let pred = self.combining(l, r);
                self.succ(pred)
            }
            _ => self.max(l, r),
        }
    }

    pub fn simplify(&mut self, ptr: LevelId) -> LevelId {
        match self.level(self.level_succs(ptr).0) {
            Zero | Param(..) => return ptr,
            _ => {}
        }
        if let Some(cached) = self.expr_cache.simplify.get(&ptr) {
            return cached;
        }
        let result = match self.level(ptr) {
            Zero | Param(..) => ptr,
            Succ(val) => {
                let val = self.simplify(val);
                self.succ(val)
            }
            Max(l, r) => {
                let l = self.simplify(l);
                let r = self.simplify(r);
                self.combining(l, r)
            }
            IMax(l, r) => {
                let l_simp = self.simplify(l);
                let r_simp = self.simplify(r);
                if self.is_always_zero(l_simp) || self.is_always_one(l_simp) {
                    r_simp
                } else {
                    match self.level(r_simp) {
                        Zero => r_simp,
                        Succ(..) => self.combining(l_simp, r_simp),
                        _ => self.imax(l_simp, r_simp),
                    }
                }
            }
        };
        self.expr_cache.simplify.insert(ptr, result);
        result
    }

    /// Return `uparams [ks |-> vs]` for a list of uparams
    pub fn subst_levels(&mut self, uparams: LevelsId, ks: LevelsId, vs: LevelsId) -> LevelsId {
        if let Some(cached) = self.subst_levels_cache.get(&(uparams, ks, vs)) {
            return cached;
        }
        let n = self.levels(uparams).len();
        let out = (0..n)
            .map(|i| {
                let l = self.levels(uparams)[i];
                self.subst_level(l, ks, vs)
            })
            .collect::<smallvec::SmallVec<[LevelId; 8]>>();
        let r = self.alloc_levels(&out);
        self.subst_levels_cache.insert((uparams, ks, vs), r);
        r
    }

    /// Return `uparam [ks |-> vs]`
    pub fn subst_level(&mut self, level: LevelId, ks: LevelsId, vs: LevelsId) -> LevelId {
        match self.level(level) {
            Zero => ZERO,
            Param(..) => {
                let (ks, vs) = (self.levels(ks), self.levels(vs));
                for (k, v) in ks.iter().copied().zip(vs.iter().copied()) {
                    if level == k {
                        return v;
                    }
                }
                level
            }
            Succ(..) | Max(..) | IMax(..) => {
                if let Some(cached) = self.subst_level_cache.get(&(level, ks, vs)) {
                    return cached;
                }
                let r = match self.level(level) {
                    Succ(val) => {
                        let val = self.subst_level(val, ks, vs);
                        self.succ(val)
                    }
                    Max(l, r) => {
                        let l_prime = self.subst_level(l, ks, vs);
                        let r_prime = self.subst_level(r, ks, vs);
                        self.max(l_prime, r_prime)
                    }
                    IMax(l, r) => {
                        let l_prime = self.subst_level(l, ks, vs);
                        let r_prime = self.subst_level(r, ks, vs);
                        self.imax(l_prime, r_prime)
                    }
                    Zero | Param(..) => unreachable!(),
                };
                self.subst_level_cache.insert((level, ks, vs), r);
                r
            }
        }
    }

    fn subst_simp(&mut self, level: LevelId, ks: LevelsId, vs: LevelsId) -> LevelId {
        let l = self.subst_level(level, ks, vs);
        self.simplify(l)
    }

    /// Test whether `lhs <= rhs` by checking whether it holds regardless of whether
    /// a parameter `p` is zero or non-zero.
    fn leq_imax_by_cases(
        &mut self,
        param: LevelId,
        lhs: LevelId,
        rhs: LevelId,
        diff: isize,
    ) -> bool {
        let succ_param = self.succ(param);
        let zero_slice = self.alloc_levels(&[ZERO]);
        let succ_param_slice = self.alloc_levels(&[succ_param]);
        let param_slice = self.alloc_levels(&[param]);

        let lhs_0 = self.subst_simp(lhs, param_slice, zero_slice);
        let rhs_0 = self.subst_simp(rhs, param_slice, zero_slice);
        let lhs_s = self.subst_simp(lhs, param_slice, succ_param_slice);
        let rhs_s = self.subst_simp(rhs, param_slice, succ_param_slice);

        self.leq_core(lhs_0, rhs_0, diff) && self.leq_core(lhs_s, rhs_s, diff)
    }

    // The more positive it is, the more have been applied to the right side compared to the left side.
    fn leq_core(&mut self, l_in: LevelId, r_in: LevelId, diff: isize) -> bool {
        match (self.level(l_in), self.level(r_in)) {
            (Zero, _) if diff >= 0 => true,
            (_, Zero) if diff < 0 => false,
            (Param(a), Param(x)) => a == x && diff >= 0,
            (Param(..), Zero) => false,
            (Zero, Param { .. }) => diff >= 0,
            (Succ(s), _) => self.leq_core(s, r_in, diff - 1),
            (_, Succ(s)) => self.leq_core(l_in, s, diff + 1),
            (Max(a, b), _) => self.leq_core(a, r_in, diff) && self.leq_core(b, r_in, diff),
            (Param(..), Max(x, y)) => self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff),
            (Zero, Max(x, y)) => self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff),
            (IMax(a, b), IMax(x, y)) if (a == x) && (b == y) && diff >= 0 => true,
            (IMax(_, b), _) if self.is_param(b) => self.leq_imax_by_cases(b, l_in, r_in, diff),

            (_, IMax(_, y)) if self.is_param(y) => self.leq_imax_by_cases(y, l_in, r_in, diff),

            (IMax(a, b), _) if self.is_any_max(b) => match self.level(b) {
                IMax(x, y) => {
                    let new_lhs = self.imax(a, y);
                    let new_rhs = self.imax(x, y);
                    let new_max = self.max(new_lhs, new_rhs);
                    self.leq_core(new_max, r_in, diff)
                }
                Max(x, y) => {
                    let new_lhs = self.imax(a, x);
                    let new_rhs = self.imax(a, y);
                    let new_max = self.max(new_lhs, new_rhs);
                    let new_max = self.simplify(new_max);
                    self.leq_core(new_max, r_in, diff)
                }
                _ => panic!(),
            },
            (_, IMax(x, y)) if self.is_any_max(y) => match self.level(y) {
                IMax(j, k) => {
                    let new_lhs = self.imax(x, k);
                    let new_rhs = self.imax(j, k);
                    let new_max = self.max(new_lhs, new_rhs);
                    self.leq_core(l_in, new_max, diff)
                }
                Max(j, k) => {
                    let new_lhs = self.imax(x, j);
                    let new_rhs = self.imax(x, k);
                    let new_rhs = self.max(new_lhs, new_rhs);
                    let new_rhs = self.simplify(new_rhs);
                    self.leq_core(l_in, new_rhs, diff)
                }
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    pub fn leq(&mut self, l: LevelId, r: LevelId) -> bool {
        if l == r {
            return true;
        }
        if let Some(cached) = self.leq_cache.get(&(l, r)) {
            return cached;
        }
        let l_prime = self.simplify(l);
        let r_prime = self.simplify(r);
        let result = self.leq_core(l_prime, r_prime, 0);
        self.leq_cache.insert((l, r), result);
        result
    }

    pub fn eq_antisymm(&mut self, l: LevelId, r: LevelId) -> bool {
        l == r || (self.leq(l, r) && self.leq(r, l))
    }

    pub fn eq_antisymm_many(&mut self, xs: LevelsId, ys: LevelsId) -> bool {
        if xs == ys {
            return true;
        }
        let n = self.levels(xs).len();
        if n != self.levels(ys).len() {
            return false;
        }
        (0..n).all(|i| {
            let (x, y) = (self.levels(xs)[i], self.levels(ys)[i]);
            self.eq_antisymm(x, y)
        })
    }

    // 1 <= level -> is_nonzero(level)
    pub fn is_nonzero(&mut self, level: LevelId) -> bool {
        let one = self.succ(ZERO);
        self.leq(one, level)
    }

    pub(crate) fn is_always_zero(&self, l: LevelId) -> bool {
        match self.level(l) {
            Zero => true,
            Succ(..) | Param(..) => false,
            Max(l, r) => self.is_always_zero(l) && self.is_always_zero(r),
            IMax(_, r) => self.is_always_zero(r),
        }
    }

    pub(crate) fn is_zero_under(&self, l: LevelId, params: &[LevelId], args: &[LevelId]) -> bool {
        match self.level(l) {
            Zero => true,
            Succ(..) => false,
            Param(..) => params
                .iter()
                .position(|p| *p == l)
                .is_some_and(|i| self.is_always_zero(args[i])),
            Max(a, b) => self.is_zero_under(a, params, args) && self.is_zero_under(b, params, args),
            IMax(_, b) => self.is_zero_under(b, params, args),
        }
    }

    fn is_always_one(&self, l: LevelId) -> bool {
        match self.level(l) {
            Succ(pred) => self.is_always_zero(pred),
            _ => false,
        }
    }

    pub(crate) fn level_succs(&self, mut l: LevelId) -> (LevelId, usize) {
        let mut num_succs = 0usize;
        while let Succ(pred) = self.level(l) {
            l = pred;
            num_succs += 1;
        }
        (l, num_succs)
    }

    /// for some level `l` and list of params `ps`, assert that:\
    /// `forall Param(n) e. l, n e. params`
    pub(crate) fn all_uparams_defined(&self, l: LevelId, params: LevelsId) -> bool {
        match self.level(l) {
            Zero => true,
            Succ(val) => self.all_uparams_defined(val, params),
            Max(a, b) | IMax(a, b) => {
                self.all_uparams_defined(a, params) && self.all_uparams_defined(b, params)
            }
            Param(..) => self.levels(params).contains(&l),
        }
    }

    fn is_any_max(&self, l: LevelId) -> bool {
        matches!(self.level(l), Max(..) | IMax(..))
    }

    fn is_param(&self, l: LevelId) -> bool {
        matches!(self.level(l), Param(..))
    }

    /// returns `true` iff every element in `ls` is a `Param`, and `ls` has no duplicate elements.
    pub(crate) fn no_dupes_all_params(&self, ls: LevelsId) -> bool {
        let mut set = crate::term::hash::new_fx_hash_set();
        for l in self.levels(ls).iter().copied() {
            match self.level(l) {
                Param(..) => {
                    if set.contains(&l) {
                        return false;
                    }
                    set.insert(l);
                }
                _ => return false,
            }
        }
        true
    }

    /// Does this list of universe parameters already contain `Param(n)` for some `n : Name`
    ///
    /// Used for generating a unique elim universe in the inductive module
    pub(crate) fn contains_param(&self, ls: LevelsId, candidate: NameId) -> bool {
        self.levels(ls)
            .iter()
            .any(|&l| matches!(self.level(l), Param(n) if n == candidate))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::Config;
    use crate::frontend::parser::parse_export_file;
    use rand::random;
    use std::error::Error;
    use std::io;

    fn test_ctx<A>(f: impl FnOnce(&mut TcCtx) -> A) -> Result<A, Box<dyn Error>> {
        let export_file = parse_export_file(io::empty(), Config::default())?;
        Ok(export_file.with_ctx(|ctx, _cache, _arena| f(ctx)))
    }

    impl TcCtx<'_> {
        fn level_n(&mut self, mut level: LevelId, n: u64) -> LevelId {
            for _ in 0..n {
                level = self.succ(level);
            }
            level
        }

        fn param_quick(&mut self, name: &'static str) -> LevelId {
            let name = self.str1(name);
            self.param(name)
        }
    }

    #[test]
    fn max_self() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            let z = ctx.zero();
            let s = ctx.succ(z);
            let m = ctx.max(s, s);
            assert!(ctx.leq(s, m));
            assert!(ctx.leq(m, s));
            assert!(ctx.eq_antisymm(s, m));
        })
    }

    #[test]
    fn imax_zero() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            let z = ctx.zero();
            let s = ctx.succ(z);
            let ss = ctx.succ(s);
            let im = ctx.imax(ss, z);
            assert!(ctx.leq(im, z));
            assert!(ctx.eq_antisymm(z, im));
        })
    }

    #[test]
    fn param_incomparable() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            let a = ctx.param_quick("a");
            let b = ctx.param_quick("b");
            assert!(!ctx.leq(a, b));
            assert!(!ctx.leq(b, a));
        })
    }

    #[test]
    fn imax_le_succ() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            let a = ctx.param_quick("a");
            let b = ctx.param_quick("b");
            let imax_a_b = ctx.imax(a, b);
            let s_imax_a_b = ctx.succ(imax_a_b);
            let ss_imax_a_b = ctx.succ(s_imax_a_b);
            assert!(ctx.leq(imax_a_b, imax_a_b));
            assert!(ctx.leq(imax_a_b, s_imax_a_b));
            assert!(ctx.leq(imax_a_b, ss_imax_a_b));
            assert!(ctx.leq(s_imax_a_b, ss_imax_a_b));
            assert!(!ctx.leq(ss_imax_a_b, imax_a_b));
            assert!(!ctx.leq(ss_imax_a_b, s_imax_a_b));
        })
    }

    #[test]
    fn succ_le_succ() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            for _ in 0..100 {
                let (small, large) = {
                    let (x, y): (u8, u8) = random();
                    (x.min(y), x.max(y))
                };

                let p = ctx.param_quick("p");
                let (a, b) = (
                    ctx.level_n(p, u64::from(small)),
                    ctx.level_n(p, u64::from(large)),
                );
                assert!(ctx.leq(a, b));
            }
        })
    }

    #[test]
    fn max_le_max() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            let (p, q) = (ctx.param_quick("p"), ctx.param_quick("q"));
            for _ in 0..100 {
                let (small, large) = {
                    let (x, y): (u8, u8) = random();
                    (u64::from(x.min(y)), u64::from(x.max(y)))
                };
                let lhs = {
                    let (p_small, q_small) = (ctx.level_n(p, small), ctx.level_n(q, small));
                    let lhs = ctx.max(p_small, q_small);
                    ctx.level_n(lhs, small)
                };
                let rhs = {
                    let (p_large, q_large) = (ctx.level_n(p, large), ctx.level_n(q, large));
                    let rhs = ctx.max(p_large, q_large);
                    ctx.level_n(rhs, large)
                };

                assert!(ctx.leq(lhs, rhs));
            }
        })
    }

    #[test]
    fn imax_le_imax() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            let (p, q) = (ctx.param_quick("p"), ctx.param_quick("q"));
            for _ in 0..100 {
                let (small, large) = {
                    let (x, y): (u8, u8) = random();
                    (u64::from(x.min(y)), u64::from(x.max(y)))
                };
                let lhs = {
                    let (p_small, q_small) = (ctx.level_n(p, small), ctx.level_n(q, small));
                    let lhs = ctx.imax(p_small, q_small);
                    ctx.level_n(lhs, small)
                };
                let rhs = {
                    let (p_large, q_large) = (ctx.level_n(p, large), ctx.level_n(q, large));
                    let rhs = ctx.imax(p_large, q_large);
                    ctx.level_n(rhs, large)
                };

                assert!(ctx.leq(lhs, rhs));
            }
        })
    }

    #[test]
    fn imax_eq_max_of_pos() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            let (p, q) = (ctx.param_quick("p"), ctx.param_quick("q"));
            for _ in 0..100 {
                let (u, v, w) = {
                    let (u, v, w): (u8, u8, u8) = random();
                    (u64::from(u), u64::from(v), u64::from(w))
                };
                let lhs = {
                    let (p_, q_) = (ctx.level_n(p, u), ctx.level_n(q, v + 1));
                    let lhs = ctx.imax(p_, q_);
                    ctx.level_n(lhs, w)
                };
                let rhs = {
                    let (p_, q_) = (ctx.level_n(p, u), ctx.level_n(q, v + 1));
                    let rhs = ctx.max(p_, q_);
                    ctx.level_n(rhs, w)
                };

                assert!(ctx.eq_antisymm(lhs, rhs));
            }
        })
    }

    #[test]
    fn succ_max_self() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            let z = ctx.zero();
            let s = ctx.succ(z);
            let ss = ctx.succ(s);
            let m = ctx.max(s, s);
            let sm = ctx.succ(m);
            assert!(ctx.eq_antisymm(ss, sm));
        })
    }

    #[test]
    fn eq_antisymm_many_max_self() -> Result<(), Box<dyn Error>> {
        // [2] == [max(1, 1) + 1]
        test_ctx(|ctx| {
            let z = ctx.zero();
            let s = ctx.succ(z);
            let ss = ctx.succ(s);
            let m = ctx.max(s, s);
            let sm = ctx.succ(m);
            let ups1 = ctx.alloc_levels(&[ss]);
            let ups2 = ctx.alloc_levels(&[sm]);
            assert!(ctx.eq_antisymm_many(ups1, ups2));
        })
    }

    #[test]
    fn repr_succ() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            let z = ctx.zero();
            let s = ctx.succ(z);
            let ss = ctx.succ(s);
            let (z_, num) = ctx.level_succs(ss);
            assert_eq!(z_, z);
            assert_eq!(num, 2);
            assert_eq!("2", format!("{:?}", ctx.debug_print(ss)));
        })
    }

    #[test]
    fn repr_succ_max() -> Result<(), Box<dyn Error>> {
        test_ctx(|ctx| {
            let z = ctx.zero();
            let s = ctx.succ(z);
            let m = ctx.max(s, s);
            let sm = ctx.succ(m);
            let (m_, num) = ctx.level_succs(sm);
            assert_eq!(m, m_);
            assert_eq!(num, 1);
            assert_eq!("max(1, 1) + 1", format!("{:?}", ctx.debug_print(sm)));
        })
    }
}
