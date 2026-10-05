// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

//! Implementation of the `Level` type representing universes
use crate::checker::context::TcCtx;
use crate::term::ptr::{LevelPtr, LevelsPtr, NamePtr};

pub(crate) const ZERO_HASH: u64 = 283;
pub(crate) const SUCC_HASH: u64 = 541;
pub(crate) const MAX_HASH: u64 = 1091;
pub(crate) const IMAX_HASH: u64 = 1747;
pub(crate) const PARAM_HASH: u64 = 947;
use Level::{IMax, Max, Param, Succ, Zero};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level<'a> {
    Zero,
    Succ(LevelPtr<'a>, u64),
    Max(LevelPtr<'a>, LevelPtr<'a>, u64),
    IMax(LevelPtr<'a>, LevelPtr<'a>, u64),
    Param(NamePtr<'a>, u64),
}

impl Level<'_> {
    fn get_hash(&self) -> u64 {
        match self {
            Zero => ZERO_HASH,
            Succ(.., hash) | Max(.., hash) | IMax(.., hash) | Param(.., hash) => *hash,
        }
    }
}

impl std::hash::Hash for Level<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.get_hash());
    }
}

impl crate::term::hash::RawHash for Level<'_> {
    #[inline]
    fn raw_hash(&self) -> u64 {
        self.get_hash()
    }
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    fn combining(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        match (*l, *r) {
            (Zero, _) => r,
            (_, Zero) => l,
            (Succ(l, ..), Succ(r, ..)) => {
                let pred = self.combining(l, r);
                self.succ(pred)
            }
            _ => self.max(l, r),
        }
    }

    pub fn simplify(&mut self, ptr: LevelPtr<'t>) -> LevelPtr<'t> {
        match *ptr {
            Zero | Param(..) => return ptr,
            _ => {}
        }
        if let Some(cached) = self.expr_cache.simplify.get(&ptr).copied() {
            return cached;
        }
        let result = match *ptr {
            Zero | Param(..) => ptr,
            Succ(val, ..) => {
                let val = self.simplify(val);
                self.succ(val)
            }
            Max(l, r, ..) => {
                let l = self.simplify(l);
                let r = self.simplify(r);
                self.combining(l, r)
            }
            IMax(l, r, ..) => {
                let l_simp = self.simplify(l);
                let r_simp = self.simplify(r);
                if self.is_zero(l_simp) || self.is_one(l_simp) {
                    r_simp
                } else {
                    match *r_simp {
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
    pub fn subst_levels(
        &mut self,
        uparams: LevelsPtr<'t>,
        ks: LevelsPtr<'t>,
        vs: LevelsPtr<'t>,
    ) -> LevelsPtr<'t> {
        if let Some(cached) = self.subst_levels_cache.get(&(uparams, ks, vs)).copied() {
            return cached;
        }
        let out = uparams
            .as_ref()
            .iter()
            .copied()
            .map(|l| self.subst_level(l, ks, vs))
            .collect::<Vec<_>>();
        let r = self.alloc_levels(&out);
        self.subst_levels_cache.insert((uparams, ks, vs), r);
        r
    }

    /// Return `uparam [ks |-> vs]`
    pub fn subst_level(
        &mut self,
        level: LevelPtr<'t>,
        ks: LevelsPtr<'t>,
        vs: LevelsPtr<'t>,
    ) -> LevelPtr<'t> {
        match *level {
            Zero => self.zero(),
            Param(..) => {
                let (ks, vs) = (ks.as_ref(), vs.as_ref());
                for (k, v) in ks.iter().copied().zip(vs.iter().copied()) {
                    if level == k {
                        return v;
                    }
                }
                level
            }
            Succ(..) | Max(..) | IMax(..) => {
                if let Some(cached) = self.subst_level_cache.get(&(level, ks, vs)).copied() {
                    return cached;
                }
                let r = match *level {
                    Succ(val, ..) => {
                        let val = self.subst_level(val, ks, vs);
                        self.succ(val)
                    }
                    Max(l, r, ..) => {
                        let l_prime = self.subst_level(l, ks, vs);
                        let r_prime = self.subst_level(r, ks, vs);
                        self.max(l_prime, r_prime)
                    }
                    IMax(l, r, ..) => {
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

    fn subst_simp(
        &mut self,
        level: LevelPtr<'t>,
        ks: LevelsPtr<'t>,
        vs: LevelsPtr<'t>,
    ) -> LevelPtr<'t> {
        let l = self.subst_level(level, ks, vs);
        self.simplify(l)
    }

    /// Test whether `lhs <= rhs` by checking whether it holds regardless of whether
    /// a parameter `p` is zero or non-zero.
    fn leq_imax_by_cases(
        &mut self,
        param: LevelPtr<'t>,
        lhs: LevelPtr<'t>,
        rhs: LevelPtr<'t>,
        diff: isize,
    ) -> bool {
        let zero = self.zero();
        let succ_param = self.succ(param);
        let zero_slice = self.alloc_levels_slice(&[zero]);
        let succ_param_slice = self.alloc_levels_slice(&[succ_param]);
        let param_slice = self.alloc_levels_slice(&[param]);

        let lhs_0 = self.subst_simp(lhs, param_slice, zero_slice);
        let rhs_0 = self.subst_simp(rhs, param_slice, zero_slice);
        let lhs_s = self.subst_simp(lhs, param_slice, succ_param_slice);
        let rhs_s = self.subst_simp(rhs, param_slice, succ_param_slice);

        self.leq_core(lhs_0, rhs_0, diff) && self.leq_core(lhs_s, rhs_s, diff)
    }

    // The more positive it is, the more have been applied to the right side compared to the left side.
    fn leq_core(&mut self, l_in: LevelPtr<'t>, r_in: LevelPtr<'t>, diff: isize) -> bool {
        match (*l_in, *r_in) {
            (Zero, _) if diff >= 0 => true,
            (_, Zero) if diff < 0 => false,
            (Param(a, ..), Param(x, ..)) => a == x && diff >= 0,
            (Param(..), Zero) => false,
            (Zero, Param { .. }) => diff >= 0,
            (Succ(s, ..), _) => self.leq_core(s, r_in, diff - 1),
            (_, Succ(s, ..)) => self.leq_core(l_in, s, diff + 1),
            (Max(a, b, ..), _) => self.leq_core(a, r_in, diff) && self.leq_core(b, r_in, diff),
            (Param(..), Max(x, y, ..)) => {
                self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff)
            }
            (Zero, Max(x, y, ..)) => self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff),
            (IMax(a, b, ..), IMax(x, y, ..)) if (a == x) && (b == y) && diff >= 0 => true,
            (IMax(_, b, _), _) if b.is_param() => self.leq_imax_by_cases(b, l_in, r_in, diff),

            (_, IMax(_, y, _)) if y.is_param() => self.leq_imax_by_cases(y, l_in, r_in, diff),

            (IMax(a, b, ..), _) if b.is_any_max() => match *b {
                IMax(x, y, ..) => {
                    let new_lhs = self.imax(a, y);
                    let new_rhs = self.imax(x, y);
                    let new_max = self.max(new_lhs, new_rhs);
                    self.leq_core(new_max, r_in, diff)
                }
                Max(x, y, ..) => {
                    let new_lhs = self.imax(a, x);
                    let new_rhs = self.imax(a, y);
                    let new_max = self.max(new_lhs, new_rhs);
                    let new_max = self.simplify(new_max);
                    self.leq_core(new_max, r_in, diff)
                }
                _ => panic!(),
            },
            (_, IMax(x, y, ..)) if y.is_any_max() => match *y {
                IMax(j, k, ..) => {
                    let new_lhs = self.imax(x, k);
                    let new_rhs = self.imax(j, k);
                    let new_max = self.max(new_lhs, new_rhs);
                    self.leq_core(l_in, new_max, diff)
                }
                Max(j, k, ..) => {
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

    pub fn leq(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> bool {
        if l == r {
            return true;
        }
        if let Some(cached) = self.leq_cache.get(&(l, r)).copied() {
            return cached;
        }
        let l_prime = self.simplify(l);
        let r_prime = self.simplify(r);
        let result = self.leq_core(l_prime, r_prime, 0);
        self.leq_cache.insert((l, r), result);
        result
    }

    pub fn eq_antisymm(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> bool {
        l == r || (self.leq(l, r) && self.leq(r, l))
    }

    pub fn eq_antisymm_many(&mut self, xs: LevelsPtr<'t>, ys: LevelsPtr<'t>) -> bool {
        if xs == ys {
            return true;
        }
        let xs = xs.as_ref();
        let ys = ys.as_ref();
        if xs.len() != ys.len() {
            return false;
        }
        xs.iter()
            .copied()
            .zip(ys.iter().copied())
            .all(|(x, y)| self.eq_antisymm(x, y))
    }

    fn is_one(&mut self, l: LevelPtr<'t>) -> bool {
        match *l {
            Level::Succ(pred, _) => self.is_zero(pred),
            _ => false,
        }
    }

    /// l <= 0 -> `is_zero(l)`
    pub fn is_zero(&mut self, level: LevelPtr<'t>) -> bool {
        let zero = self.zero();
        self.leq(level, zero)
    }

    // 1 <= level -> is_nonzero(level)
    pub fn is_nonzero(&mut self, level: LevelPtr<'t>) -> bool {
        let zero = self.zero();
        let one = self.succ(zero);
        self.leq(one, level)
    }
}

impl<'t> LevelPtr<'t> {
    pub(crate) fn level_succs(mut self) -> (LevelPtr<'t>, usize) {
        let mut num_succs = 0usize;
        while let Succ(pred, ..) = *self {
            self = pred;
            num_succs += 1;
        }
        (self, num_succs)
    }

    /// for some level `l` and list of params `ps`, assert that:\
    /// `forall Param(n) e. l, n e. params`
    pub(crate) fn all_uparams_defined(self, params: LevelsPtr<'t>) -> bool {
        match *self {
            Zero => true,
            Succ(val, ..) => val.all_uparams_defined(params),
            Max(l, r, ..) | IMax(l, r, ..) => {
                l.all_uparams_defined(params) && r.all_uparams_defined(params)
            }
            Param(..) => params.as_ref().iter().copied().any(|x| x == self),
        }
    }

    fn is_any_max(self) -> bool {
        matches!(*self, Max(..) | IMax(..))
    }

    fn is_param(self) -> bool {
        matches!(*self, Param(..))
    }
}

impl<'t> LevelsPtr<'t> {
    /// returns `true` iff every element in `ls` is a `Param`, and `ls` has no duplicate elements.
    pub(crate) fn no_dupes_all_params(self) -> bool {
        let mut set = crate::term::hash::new_fx_hash_set();
        for l in self.as_ref().iter().copied() {
            match *l {
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
    pub(crate) fn contains_param(self, candidate: NamePtr<'t>) -> bool {
        self.as_ref().iter().copied().any(|lptr| match *lptr {
            Param(n, ..) => n == candidate,
            _ => false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::Config;
    use crate::frontend::parser::parse_export_file;
    use bumpalo::Bump;
    use rand::random;
    use std::error::Error;

    fn test_ctx<A>(f: impl FnOnce(&mut TcCtx) -> A) -> Result<A, Box<dyn Error>> {
        let arena = Bump::new();
        let (export_file, _) = parse_export_file(&arena, std::io::empty(), Config::default())?;
        Ok(export_file.with_ctx(|ctx, _cache, _arena| f(ctx)))
    }

    impl<'t, 'p: 't> TcCtx<'t, 'p> {
        fn level_n(&mut self, mut level: LevelPtr<'t>, n: u64) -> LevelPtr<'t> {
            for _ in 0..n {
                level = self.succ(level);
            }
            level
        }

        fn param_quick(&mut self, name: &'static str) -> LevelPtr<'t> {
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
            let (z_, num) = ss.level_succs();
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
            let (m_, num) = sm.level_succs();
            assert_eq!(m, m_);
            assert_eq!(num, 1);
            assert_eq!("max(1, 1) + 1", format!("{:?}", ctx.debug_print(sm)));
        })
    }
}
