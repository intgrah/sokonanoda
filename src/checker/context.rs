// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use super::cache::{ExprCache, Reset, SESSION, SMALL, TcCache};
use super::ptrmap::{PtrMap, PtrSet};
use crate::checker::env::{DeclarMap, Env, EnvLimit};
use crate::checker::relevance::{Sig, SigTemplate};
use crate::checker::tc::TypeChecker;
use crate::config::Config;
use crate::term::expr::{Expr, ExprNode};
use crate::term::hash::{FxHashMap, FxHashSet, GOLDEN};
use crate::term::id::{ANON, BigId, ExprId, LOCAL, LevelId, LevelsId, NameId, StrId, ZERO};
use crate::term::intern::{NameCache, Terms};
use crate::term::level::Level;
use crate::term::name::{Name, NameDisplay, NameSource, NatRed};
use bumpalo::Bump;
use num_bigint::BigUint;
use rustc_hash::FxBuildHasher;
use std::sync::Arc;

pub struct ExportFile {
    pub(crate) terms: Terms,
    pub(crate) declars: DeclarMap,
    pub(crate) decl_of: Vec<u32>,
    pub(crate) nat_red: Vec<Option<NatRed>>,
    pub(crate) name_cache: NameCache,
    pub(crate) config: Config,
    pub(crate) mutual_block_sizes: FxHashMap<NameId, (usize, usize)>,
}

impl NameSource for Terms {
    fn name(&self, n: NameId) -> Name {
        assert!(!n.is_local(), "local name outside of a type checker");
        self.names.items[n.index()]
    }

    fn string(&self, s: StrId) -> &str {
        assert!(!s.is_local(), "local string outside of a type checker");
        &self.strings.items[s.index()]
    }
}

impl ExportFile {
    pub(crate) fn check_inductives(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .name("inductives".into())
                .stack_size(crate::STACK_SIZE)
                .spawn_scoped(scope, || {
                    let (blocks, local) = {
                        let arena = Bump::new();
                        let mut ctx = TcCtx::new(self, &arena);
                        ctx.env_ext = Some(Arc::new(crate::term::hash::new_fx_index_map()));
                        let mut blocks = Vec::new();
                        let mut next = 0;
                        while next < self.declars.len() {
                            let (_, declar) = self.declars.get_index(next).unwrap();
                            let (start, size, derived) = match declar {
                                crate::checker::env::Declar::Quot { .. } => {
                                    let mut cache = TcCache::new_small();
                                    let derived = crate::checker::quot::derive_quot(
                                        &mut ctx, &mut cache, declar,
                                    );
                                    (next, 1, vec![derived])
                                }
                                crate::checker::env::Declar::Inductive(ind) => {
                                    let &(start, size) =
                                        self.mutual_block_sizes.get(&ind.info.name).unwrap();
                                    let mut cache = TcCache::new_small();
                                    let derived =
                                        self.check_inductive_declar(&mut ctx, &mut cache, ind);
                                    (start, size, derived)
                                }
                                _ => {
                                    next += 1;
                                    continue;
                                }
                            };
                            let env_ext = Arc::get_mut(ctx.env_ext.as_mut().unwrap()).unwrap();
                            for declar in &derived {
                                env_ext.insert(declar.info().name, declar.clone());
                            }
                            blocks.push((start, size, derived));
                            next = start + size;
                        }
                        (blocks, ctx.local)
                    };
                    let mut promoter =
                        crate::checker::inductive::persist::Promoter::new(local, &mut self.terms);
                    let mut blocks = blocks.into_iter().peekable();
                    let mut declars = crate::term::hash::new_fx_index_map();
                    self.mutual_block_sizes.clear();
                    let mut skipped = 0;
                    for (idx, (name, declar)) in
                        std::mem::take(&mut self.declars).into_iter().enumerate()
                    {
                        if idx < skipped {
                            continue;
                        }
                        if blocks.peek().is_some_and(|(start, _, _)| *start == idx) {
                            let (_, size, block) = blocks.next().unwrap();
                            skipped = idx + size;
                            let start = declars.len();
                            let size = block.len();
                            for declar in block {
                                let declar = promoter.declar(declar);
                                let name = declar.info().name;
                                if matches!(declar, crate::checker::env::Declar::Inductive(_)) {
                                    self.mutual_block_sizes.insert(name, (start, size));
                                }
                                crate::outcome::ensure!(
                                    declars.insert(name, declar).is_none(),
                                    "duplicate declaration"
                                );
                            }
                        } else {
                            crate::outcome::ensure!(
                                declars.insert(name, declar).is_none(),
                                "duplicate declaration"
                            );
                        }
                    }
                    self.declars = declars;
                    self.decl_of = vec![crate::term::name::NO_DECL; self.terms.names.items.len()];
                    for (idx, (name, _)) in self.declars.iter().enumerate() {
                        self.decl_of[name.index()] =
                            u32::try_from(idx).expect("too many declarations");
                    }
                    self.nat_red = vec![None; self.terms.names.items.len()];
                    self.name_cache = self.terms.mk_name_cache(&mut self.nat_red);
                })?
                .join()
                .map_err(crate::outcome::CheckError::from_panic)
                .map_err(|error| -> Box<dyn std::error::Error> {
                    match error {
                        crate::outcome::CheckError::Rejected(error) => Box::new(error),
                        crate::outcome::CheckError::Declined(error) => Box::new(error),
                        crate::outcome::CheckError::Internal(payload) => {
                            std::panic::resume_unwind(payload)
                        }
                    }
                })
        })
    }

    pub fn num_declars(&self) -> usize {
        self.declars.len()
    }

    pub(crate) fn new_env(&self, env_limit: EnvLimit) -> Env<'_> {
        Env::new(&self.declars, &self.decl_of, env_limit)
    }

    pub(crate) fn display(&self, n: NameId) -> NameDisplay<'_, Terms> {
        NameDisplay {
            src: &self.terms,
            name: n,
        }
    }

    #[inline]
    pub(crate) fn nat_red(&self, n: NameId) -> Option<NatRed> {
        if n.is_local() {
            return None;
        }
        *self.nat_red.get(n.index())?
    }

    #[cfg(test)]
    pub(crate) fn with_ctx<F, A>(&self, f: F) -> A
    where
        F: for<'t> FnOnce(&mut TcCtx<'t>, &mut TcCache, &'t Bump) -> A,
    {
        let arena = Bump::new();
        let mut ctx = TcCtx::new(self, &arena);
        let mut cache = TcCache::new();
        f(&mut ctx, &mut cache, &arena)
    }
}

const LEAF_BITS: u32 = 12;
const LEAF_SLOTS: usize = 1 << LEAF_BITS;

pub struct TcCtx<'t> {
    pub(crate) export_file: &'t ExportFile,
    pub(crate) arena: &'t Bump,
    global: &'t Terms,
    global_exprs: &'t [ExprNode],
    expr_bases: [*const ExprNode; 2],
    local: Terms,
    pub(crate) env_ext: Option<Arc<DeclarMap>>,
    pub(crate) expr_cache: ExprCache,
    pub(crate) sig_cache: PtrMap<(NameId, LevelsId), Sig>,
    pub(crate) sig_templates: PtrMap<NameId, SigTemplate<'t>>,
    pub(crate) sig_computing: FxHashSet<NameId>,
    pub(crate) subst_level_cache: PtrMap<(LevelId, LevelsId, LevelsId), LevelId>,
    pub(crate) leq_cache: PtrMap<(LevelId, LevelId), bool>,
    pub(crate) checked_closed: PtrSet<(ExprId, LevelsId)>,
    leaf_checked: Box<[(u32, u32)]>,
    leaf_stamp: u32,
    pub(crate) subst_levels_cache: PtrMap<(LevelsId, LevelsId, LevelsId), LevelsId>,
}

impl NameSource for TcCtx<'_> {
    fn name(&self, n: NameId) -> Name {
        TcCtx::name(self, n)
    }

    fn string(&self, s: StrId) -> &str {
        TcCtx::string(self, s)
    }
}

impl<'t> TcCtx<'t> {
    pub(crate) fn new_env(&self, limit: EnvLimit) -> Env<'t> {
        self.export_file
            .new_env(limit)
            .with_env_ext(self.env_ext.clone())
    }

    pub fn new(export_file: &'t ExportFile, arena: &'t Bump) -> Self {
        Self {
            export_file,
            arena,
            global: &export_file.terms,
            global_exprs: &export_file.terms.exprs.items,
            expr_bases: [export_file.terms.exprs.items.as_ptr(), local_expr_base(&[])],
            local: Terms::default(),
            env_ext: None,
            expr_cache: ExprCache::new(),
            sig_cache: Reset::with_cap(SESSION),
            sig_templates: Reset::with_cap(SMALL),
            sig_computing: FxHashSet::with_capacity_and_hasher(SMALL, FxBuildHasher),
            subst_level_cache: Reset::with_cap(SMALL),
            leq_cache: Reset::with_cap(SMALL),
            checked_closed: Reset::with_cap(SMALL),
            leaf_checked: vec![(0, 0); LEAF_SLOTS].into_boxed_slice(),
            leaf_stamp: 1,
            subst_levels_cache: Reset::with_cap(SMALL),
        }
    }

    #[inline(always)]
    fn terms(&self, local: bool) -> &Terms {
        if local { &self.local } else { self.global }
    }

    #[inline(always)]
    pub(crate) fn node(&self, e: ExprId) -> &ExprNode {
        debug_assert!(
            e.index()
                < if e.is_local() {
                    self.local.exprs.items.len()
                } else {
                    self.global_exprs.len()
                }
        );
        let raw = e.raw();
        unsafe { &*self.expr_bases[(raw >> 31) as usize].wrapping_add(raw as usize) }
    }

    #[inline(always)]
    pub(crate) fn ex(&self, e: ExprId) -> Expr {
        self.node(e).expr
    }

    #[inline(always)]
    pub(crate) fn loose(&self, e: ExprId) -> u16 {
        self.node(e).loose
    }

    #[inline(always)]
    pub(crate) fn mask(&self, e: ExprId) -> u64 {
        self.node(e).mask
    }

    #[inline(always)]
    pub(crate) fn level(&self, l: LevelId) -> Level {
        self.terms(l.is_local()).levels.items[l.index()]
    }

    #[inline(always)]
    pub(crate) fn levels(&self, ls: LevelsId) -> &[LevelId] {
        &self.terms(ls.is_local()).lists.items[ls.index()]
    }

    #[inline(always)]
    pub(crate) fn name(&self, n: NameId) -> Name {
        self.terms(n.is_local()).names.items[n.index()]
    }

    #[inline(always)]
    pub(crate) fn string(&self, s: StrId) -> &str {
        &self.terms(s.is_local()).strings.items[s.index()]
    }

    #[inline(always)]
    pub(crate) fn bignum(&self, b: BigId) -> &BigUint {
        &self.terms(b.is_local()).bignums.items[b.index()]
    }

    pub(crate) fn display(&self, n: NameId) -> NameDisplay<'_, Self> {
        NameDisplay { src: self, name: n }
    }

    pub(crate) fn next_declaration(&mut self) {
        self.leaf_stamp = self.leaf_stamp.wrapping_add(1);
        if self.leaf_stamp == 0 {
            self.leaf_checked.fill((0, 0));
            self.leaf_stamp = 1;
        }
    }

    #[inline]
    fn leaf_slot(e: ExprId) -> usize {
        let h = u64::from(e.raw()).wrapping_mul(GOLDEN) >> (u64::BITS - LEAF_BITS);
        usize::try_from(h).expect("usize is 64 bits wide")
    }

    #[inline]
    pub(crate) fn leaf_checked(&self, e: ExprId) -> bool {
        self.leaf_checked[Self::leaf_slot(e)] == (e.raw(), self.leaf_stamp)
    }

    #[inline]
    pub(crate) fn mark_leaf_checked(&mut self, e: ExprId) {
        self.leaf_checked[Self::leaf_slot(e)] = (e.raw(), self.leaf_stamp);
    }

    pub fn with_tc<F, A>(&mut self, env_limit: EnvLimit, cache: &mut TcCache, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't>) -> A,
    {
        let env = self.new_env(env_limit);
        let mut tc = TypeChecker::new(self, &env, None, cache);
        f(&mut tc)
    }

    pub fn with_tc_and_env_ext<'x, F, A>(
        &mut self,
        env_ext: &'x DeclarMap,
        env_limit: EnvLimit,
        cache: &mut TcCache,
        f: F,
    ) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't>) -> A,
    {
        let export_file = self.export_file;
        let env = Env::new_w_temp_ext(
            &export_file.declars,
            &export_file.decl_of,
            Some(env_ext),
            env_limit,
        )
        .with_env_ext(self.env_ext.clone());
        let mut tc = TypeChecker::new(self, &env, None, cache);
        f(&mut tc)
    }

    pub fn alloc_name(&mut self, n: Name) -> NameId {
        if let Some(i) = self.global.names.find(&n) {
            return NameId::new(i, false);
        }
        NameId::new(self.local.names.intern(n), true)
    }

    pub fn alloc_level(&mut self, l: Level) -> LevelId {
        if let Some(i) = self.global.levels.find(&l) {
            return LevelId::new(i, false);
        }
        LevelId::new(self.local.levels.intern(l), true)
    }

    pub fn alloc_expr(&mut self, node: ExprNode) -> ExprId {
        let i = self.local.exprs.intern(node);
        self.expr_bases[1] = local_expr_base(&self.local.exprs.items);
        ExprId::new(i, true)
    }

    pub(crate) fn alloc_string(&mut self, s: &str) -> StrId {
        if let Some(i) = self.global.strings.find(s) {
            return StrId::new(i, false);
        }
        StrId::new(self.local.strings.intern_ref(s), true)
    }

    pub(crate) fn alloc_bignum(&mut self, n: BigUint) -> Option<BigId> {
        if !self.export_file.config.nat_extension {
            return None;
        }
        if let Some(i) = self.global.bignums.find(&n) {
            return Some(BigId::new(i, false));
        }
        Some(BigId::new(self.local.bignums.intern(n), true))
    }

    pub fn alloc_levels(&mut self, ls: &[LevelId]) -> LevelsId {
        if let Some(i) = self.global.lists.find(ls) {
            return LevelsId::new(i, false);
        }
        LevelsId::new(self.local.lists.intern_ref(ls), true)
    }

    pub fn str(&mut self, pfx: NameId, sfx: StrId) -> NameId {
        self.alloc_name(Name::Str(pfx, sfx))
    }

    pub fn str1(&mut self, s: &'static str) -> NameId {
        let s = self.alloc_string(s);
        self.str(ANON, s)
    }

    pub fn str2(&mut self, s1: &'static str, s2: &'static str) -> NameId {
        let s1 = self.alloc_string(s1);
        let s2 = self.alloc_string(s2);
        let n = self.str(ANON, s1);
        self.str(n, s2)
    }

    pub fn zero(&self) -> LevelId {
        ZERO
    }

    pub fn num(&mut self, pfx: NameId, sfx: u64) -> NameId {
        self.alloc_name(Name::Num(pfx, sfx))
    }

    pub fn succ(&mut self, l: LevelId) -> LevelId {
        self.alloc_level(Level::Succ(l))
    }

    pub fn max(&mut self, l: LevelId, r: LevelId) -> LevelId {
        self.alloc_level(Level::Max(l, r))
    }

    pub fn imax(&mut self, l: LevelId, r: LevelId) -> LevelId {
        self.alloc_level(Level::IMax(l, r))
    }

    pub fn param(&mut self, n: NameId) -> LevelId {
        self.alloc_level(Level::Param(n))
    }

    pub fn mk_var(&mut self, dbj_idx: u16) -> ExprId {
        self.alloc_expr(ExprNode::var(dbj_idx))
    }

    pub fn mk_sort(&mut self, level: LevelId) -> ExprId {
        self.alloc_expr(ExprNode::leaf(Expr::Sort { level }))
    }

    pub fn mk_const(&mut self, name: NameId, levels: LevelsId) -> ExprId {
        self.alloc_expr(ExprNode::leaf(Expr::Const { name, levels }))
    }

    pub fn mk_app(&mut self, fun: ExprId, arg: ExprId) -> ExprId {
        let node = ExprNode::app(fun, self.node(fun), arg, self.node(arg));
        self.alloc_expr(node)
    }

    pub fn mk_lambda(&mut self, binder_type: ExprId, body: ExprId) -> ExprId {
        let node = ExprNode::lambda(binder_type, self.node(binder_type), body, self.node(body));
        self.alloc_expr(node)
    }

    pub fn mk_pi(&mut self, binder_type: ExprId, body: ExprId) -> ExprId {
        let node = ExprNode::pi(binder_type, self.node(binder_type), body, self.node(body));
        self.alloc_expr(node)
    }

    pub fn mk_let(
        &mut self,
        binder_type: ExprId,
        val: ExprId,
        body: ExprId,
        nondep: bool,
    ) -> ExprId {
        let node = ExprNode::let_(
            binder_type,
            self.node(binder_type),
            val,
            self.node(val),
            body,
            self.node(body),
            nondep,
        );
        self.alloc_expr(node)
    }

    pub fn mk_proj(&mut self, ty_name: NameId, idx: u16, structure: ExprId) -> ExprId {
        let node = ExprNode::proj(ty_name, idx, structure, self.node(structure));
        self.alloc_expr(node)
    }

    pub fn mk_string_lit(&mut self, lit: StrId) -> Option<ExprId> {
        if !self.export_file.config.string_extension {
            return None;
        }
        Some(self.alloc_expr(ExprNode::leaf(Expr::StringLit { lit })))
    }

    #[cfg(test)]
    pub fn mk_string_lit_quick(&mut self, s: &str) -> Option<ExprId> {
        if !self.export_file.config.string_extension {
            return None;
        }
        let lit = self.alloc_string(s);
        self.mk_string_lit(lit)
    }

    pub fn mk_nat_lit(&mut self, lit: BigId) -> Option<ExprId> {
        if !self.export_file.config.nat_extension {
            return None;
        }
        Some(self.alloc_expr(ExprNode::leaf(Expr::NatLit { lit })))
    }

    #[cfg(test)]
    pub fn mk_nat_lit_quick(&mut self, n: BigUint) -> Option<ExprId> {
        let lit = self.alloc_bignum(n)?;
        self.mk_nat_lit(lit)
    }
}

fn local_expr_base(items: &[ExprNode]) -> *const ExprNode {
    items.as_ptr().wrapping_sub(LOCAL as usize)
}
