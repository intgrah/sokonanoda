// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use super::cache::{Reset, SESSION, SMALL, TcCache, caches};
use super::ptrmap::{PtrMap, PtrSet};
use crate::checker::env::{DeclarMap, Env, EnvLimit};
use crate::checker::tc::TypeChecker;
use crate::config::Config;
use crate::hash64;
use crate::term::expr::{
    APP_HASH, CONST_HASH, Expr, LAMBDA_HASH, LET_HASH, NAT_LIT_HASH, PI_HASH, PROJ_HASH, SORT_HASH,
    STRING_LIT_HASH, VAR_HASH,
};
use crate::term::hash::{CowStr, FxHashMap, FxHashSet};
use crate::term::intern::{Dag, NameCache};
use crate::term::level::{IMAX_HASH, Level, MAX_HASH, PARAM_HASH, SUCC_HASH};
use crate::term::name::{NUM_HASH, Name, STR_HASH};
use crate::term::ptr::{BigUintPtr, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};
use bumpalo::Bump;
use num_bigint::BigUint;

caches! {
    pub struct ExprCache<'t> {
        #[cap(SMALL)] inst: FxHashMap<(ExprPtr<'t>, u16), ExprPtr<'t>>,
        #[cap(SMALL)] subst: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
        #[cap(SMALL)] dsubst: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
        #[keep(Reset::with_cap(SMALL))] simplify: PtrMap<LevelPtr<'t>, LevelPtr<'t>>,
    }
    fn new();
}

pub struct ExportFile<'p> {
    pub(crate) dag: Dag<'p>,
    pub(crate) anon: NamePtr<'p>,
    pub(crate) zero: LevelPtr<'p>,
    pub(crate) declars: DeclarMap<'p>,
    pub(crate) name_cache: NameCache<'p>,
    pub(crate) config: Config,
    pub(crate) mutual_block_sizes: FxHashMap<NamePtr<'p>, (usize, usize)>,
}

impl<'p> ExportFile<'p> {
    pub fn num_declars(&self) -> usize {
        self.declars.len()
    }

    pub(crate) fn new_env(&self, env_limit: EnvLimit<'p>) -> Env<'_, '_> {
        Env::new(&self.declars, env_limit)
    }

    #[cfg(test)]
    pub(crate) fn with_ctx<F, A>(&self, f: F) -> A
    where
        F: for<'t> FnOnce(&mut TcCtx<'t, 'p>, &mut TcCache<'t, 't>, &'t Bump) -> A,
    {
        let arena = Bump::new();
        let mut ctx = TcCtx::new(self, &arena);
        let mut cache = TcCache::new(&arena);
        f(&mut ctx, &mut cache, &arena)
    }
}

const LEAF_BITS: u32 = 12;
const LEAF_SLOTS: usize = 1 << LEAF_BITS;

pub struct TcCtx<'t, 'p> {
    pub(crate) export_file: &'t ExportFile<'p>,
    pub(crate) arena: &'t Bump,
    pub(crate) dag: Dag<'t>,
    pub(crate) expr_cache: ExprCache<'t>,
    pub(crate) sig_cache: PtrMap<(NamePtr<'t>, LevelsPtr<'t>), crate::checker::relevance::Sig>,
    pub(crate) sig_templates: PtrMap<NamePtr<'t>, crate::checker::relevance::SigTemplate<'t>>,
    pub(crate) sig_computing: FxHashSet<NamePtr<'t>>,
    pub(crate) subst_level_cache:
        PtrMap<(LevelPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), LevelPtr<'t>>,
    pub(crate) leq_cache: PtrMap<(LevelPtr<'t>, LevelPtr<'t>), bool>,
    pub(crate) checked_closed: PtrSet<(ExprPtr<'t>, LevelsPtr<'t>)>,
    leaf_checked: Box<[(usize, u32)]>,
    leaf_stamp: u32,
    pub(crate) subst_levels_cache:
        PtrMap<(LevelsPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), LevelsPtr<'t>>,
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub fn new(export_file: &'t ExportFile<'p>, arena: &'t Bump) -> Self {
        let dag = Dag::new_local(&export_file.config);
        Self {
            export_file,
            arena,
            dag,
            expr_cache: ExprCache::new(),
            sig_cache: Reset::with_cap(SESSION),
            sig_templates: Reset::with_cap(SMALL),
            sig_computing: Reset::with_cap(SMALL),
            subst_level_cache: Reset::with_cap(SMALL),
            leq_cache: Reset::with_cap(SMALL),
            checked_closed: Reset::with_cap(SMALL),
            leaf_checked: vec![(0, 0); LEAF_SLOTS].into_boxed_slice(),
            leaf_stamp: 1,
            subst_levels_cache: Reset::with_cap(SMALL),
        }
    }

    pub(crate) fn next_declaration(&mut self) {
        self.leaf_stamp = self.leaf_stamp.wrapping_add(1);
        if self.leaf_stamp == 0 {
            self.leaf_checked.fill((0, 0));
            self.leaf_stamp = 1;
        }
    }

    #[inline]
    fn leaf_slot(e: ExprPtr<'t>) -> usize {
        (e.addr().wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (usize::BITS - LEAF_BITS))
            & (LEAF_SLOTS - 1)
    }

    #[inline]
    pub(crate) fn leaf_checked(&self, e: ExprPtr<'t>) -> bool {
        self.leaf_checked[Self::leaf_slot(e)] == (e.addr(), self.leaf_stamp)
    }

    #[inline]
    pub(crate) fn mark_leaf_checked(&mut self, e: ExprPtr<'t>) {
        self.leaf_checked[Self::leaf_slot(e)] = (e.addr(), self.leaf_stamp);
    }

    pub fn with_tc<F, A>(
        &mut self,
        env_limit: EnvLimit<'p>,
        arena: &'t Bump,
        cache: &mut TcCache<'t, 't>,
        f: F,
    ) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A,
    {
        let env = self.export_file.new_env(env_limit);
        let mut tc = TypeChecker::new(self, &env, arena, None, cache);
        f(&mut tc)
    }

    pub fn with_tc_and_env_ext<'x, F, A>(
        &mut self,
        env_ext: &'x DeclarMap<'t>,
        env_limit: EnvLimit<'p>,
        arena: &'t Bump,
        cache: &mut TcCache<'t, 't>,
        f: F,
    ) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A,
    {
        let env = Env::new_w_temp_ext(&self.export_file.declars, Some(env_ext), env_limit);
        let mut tc = TypeChecker::new(self, &env, arena, None, cache);
        f(&mut tc)
    }

    pub fn alloc_name(&mut self, n: Name<'t>) -> NamePtr<'t> {
        if let Some(r) = self.export_file.dag.names.get(&n) {
            return NamePtr::global(r);
        }
        NamePtr::local(self.dag.names.intern(self.arena, n))
    }

    pub fn alloc_level(&mut self, l: Level<'t>) -> LevelPtr<'t> {
        if let Some(r) = self.export_file.dag.levels.get(&l) {
            return LevelPtr::global(r);
        }
        LevelPtr::local(self.dag.levels.intern(self.arena, l))
    }

    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        if let Some(r) = self.dag.exprs.get(&e) {
            return ExprPtr::local(r);
        }
        ExprPtr::local(self.dag.exprs.insert(self.arena, e))
    }

    pub(crate) fn alloc_string(&mut self, s: CowStr<'t>) -> StringPtr<'t> {
        if let Some(r) = self.export_file.dag.strings.get(&*s) {
            return StringPtr::global(r);
        }
        StringPtr::local(self.dag.strings.intern(self.arena, s))
    }

    pub(crate) fn alloc_bignum(&mut self, n: BigUint) -> Option<BigUintPtr<'t>> {
        if let Some(global) = self.export_file.dag.bignums.as_ref()
            && let Some(r) = global.get(&n)
        {
            return Some(BigUintPtr::global(r));
        }
        let local = self.dag.bignums.as_mut()?;
        Some(BigUintPtr::local(local.intern(self.arena, n)))
    }

    pub fn alloc_levels(&mut self, ls: &[LevelPtr<'t>]) -> LevelsPtr<'t> {
        if let Some(r) = self.export_file.dag.uparams.get(ls) {
            return LevelsPtr::global(r);
        }
        LevelsPtr::local(self.dag.uparams.intern(self.arena, ls))
    }

    pub fn alloc_levels_slice(&mut self, ls: &[LevelPtr<'t>]) -> LevelsPtr<'t> {
        self.alloc_levels(ls)
    }

    pub fn anonymous(&self) -> NamePtr<'t> {
        self.export_file.anon
    }

    pub fn str(&mut self, pfx: NamePtr<'t>, sfx: StringPtr<'t>) -> NamePtr<'t> {
        let hash = hash64!(STR_HASH, pfx, sfx);
        self.alloc_name(Name::Str(pfx, sfx, hash))
    }

    pub fn str1(&mut self, s: &'static str) -> NamePtr<'t> {
        let anon = self.alloc_name(Name::Anon);
        let s = self.alloc_string(CowStr::Borrowed(s));
        self.str(anon, s)
    }

    pub fn str2(&mut self, s1: &'static str, s2: &'static str) -> NamePtr<'t> {
        let s1 = self.alloc_string(CowStr::Borrowed(s1));
        let s2 = self.alloc_string(CowStr::Borrowed(s2));
        let n = self.anonymous();
        let n = self.str(n, s1);
        self.str(n, s2)
    }

    pub fn zero(&self) -> LevelPtr<'t> {
        self.export_file.zero
    }

    pub fn num(&mut self, pfx: NamePtr<'t>, sfx: u64) -> NamePtr<'t> {
        let hash = hash64!(NUM_HASH, pfx, sfx);
        self.alloc_name(Name::Num(pfx, sfx, hash))
    }

    pub fn succ(&mut self, l: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(SUCC_HASH, l);
        self.alloc_level(Level::Succ(l, hash))
    }

    pub fn max(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(MAX_HASH, l, r);
        self.alloc_level(Level::Max(l, r, hash))
    }
    pub fn imax(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(IMAX_HASH, l, r);
        self.alloc_level(Level::IMax(l, r, hash))
    }
    pub fn param(&mut self, n: NamePtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(PARAM_HASH, n);
        self.alloc_level(Level::Param(n, hash))
    }

    pub fn mk_var(&mut self, dbj_idx: u16) -> ExprPtr<'t> {
        let hash = hash64!(VAR_HASH, dbj_idx);
        self.alloc_expr(Expr::Var { dbj_idx, hash })
    }

    pub fn mk_sort(&mut self, level: LevelPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(SORT_HASH, level);
        self.alloc_expr(Expr::Sort { level, hash })
    }

    pub fn mk_const(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(CONST_HASH, name, levels);
        self.alloc_expr(Expr::Const { name, levels, hash })
    }

    pub fn mk_app(&mut self, fun: ExprPtr<'t>, arg: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(APP_HASH, fun, arg);
        let fv_mask = crate::term::expr::child_mask(fun) | crate::term::expr::child_mask(arg);
        self.alloc_expr(Expr::App {
            fun,
            arg,
            fv_mask,
            hash,
        })
    }

    pub fn mk_lambda(&mut self, binder_type: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(LAMBDA_HASH, binder_type, body);
        let fv_mask =
            crate::term::expr::child_mask(binder_type) | crate::term::expr::body_mask(body);
        self.alloc_expr(Expr::Lambda {
            binder_type,
            body,
            fv_mask,
            hash,
        })
    }

    pub fn mk_pi(&mut self, binder_type: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(PI_HASH, binder_type, body);
        let fv_mask =
            crate::term::expr::child_mask(binder_type) | crate::term::expr::body_mask(body);
        self.alloc_expr(Expr::Pi {
            binder_type,
            body,
            fv_mask,
            hash,
        })
    }

    pub fn mk_let(
        &mut self,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        nondep: bool,
    ) -> ExprPtr<'t> {
        let hash = hash64!(LET_HASH, binder_type, val, body, nondep);
        let fv_mask = crate::term::expr::child_mask(binder_type)
            | crate::term::expr::child_mask(val)
            | crate::term::expr::body_mask(body);
        let data = self.arena.alloc(crate::term::expr::LetData {
            binder_type,
            val,
            body,
            nondep,
        });
        self.alloc_expr(Expr::Let {
            data,
            fv_mask,
            hash,
        })
    }

    pub fn mk_proj(
        &mut self,
        ty_name: NamePtr<'t>,
        idx: u16,
        structure: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let hash = hash64!(PROJ_HASH, ty_name, idx, structure);
        let fv_mask = crate::term::expr::child_mask(structure);
        self.alloc_expr(Expr::Proj {
            ty_name,
            idx,
            structure,
            fv_mask,
            hash,
        })
    }

    pub fn mk_string_lit(&mut self, string_ptr: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.string_extension {
            return None;
        }
        let hash = hash64!(STRING_LIT_HASH, string_ptr);
        Some(self.alloc_expr(Expr::StringLit {
            ptr: string_ptr,
            hash,
        }))
    }

    #[cfg(test)]
    pub fn mk_string_lit_quick(&mut self, s: CowStr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.string_extension {
            return None;
        }
        let string_ptr = self.alloc_string(s);
        self.mk_string_lit(string_ptr)
    }

    pub fn mk_nat_lit(&mut self, num_ptr: BigUintPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.nat_extension {
            return None;
        }
        let hash = hash64!(NAT_LIT_HASH, num_ptr);
        Some(self.alloc_expr(Expr::NatLit { ptr: num_ptr, hash }))
    }

    #[cfg(test)]
    pub fn mk_nat_lit_quick(&mut self, n: BigUint) -> Option<ExprPtr<'t>> {
        let num_ptr = self.alloc_bignum(n)?;
        self.mk_nat_lit(num_ptr)
    }
}
