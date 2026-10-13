// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

//! Implementation of Lean expressions
use crate::checker::context::TcCtx;
use crate::outcome::{ensure_eq, reject};
use crate::term::hash::FxHashMap;
use crate::term::id::{BigId, ExprId, LevelId, LevelsId, NameId, StrId, ZERO};
use Expr::{App, Const, Lambda, Let, NatLit, Pi, Proj, Sort, StringLit, Var};
use num_bigint::BigUint;
use std::borrow::Borrow;
use std::hash::{Hash, Hasher};
use std::mem::MaybeUninit;
use std::slice;

pub(crate) const SPINE: usize = 16;
pub(crate) type SpineArgs = smallvec::SmallVec<[ExprId; SPINE]>;
pub(crate) type SpineBuf = [MaybeUninit<ExprId>; SPINE];

/// Binder names and plicity are presentation metadata and are deliberately omitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Expr {
    /// A string literal.
    StringLit { lit: StrId },
    /// A nat literal, an arbitrary precision bignum.
    NatLit { lit: BigId },
    Proj {
        /// The name of the structure being projected. E.g. `Prod` if this is
        /// projection 0 of `Prod.mk ..`
        ty_name: NameId,
        /// The 0-based position of the constructor argument, not considering the
        /// parameters. For some struct Foo A B, and a constructor Foo.mk A B p q r s,
        /// `q` will have idx 1.
        idx: u16,
        structure: ExprId,
    },
    /// A bound variable represented by a deBruijn index.
    Var { dbj_idx: u16 },
    Sort { level: LevelId },
    Const { name: NameId, levels: LevelsId },
    App { fun: ExprId, arg: ExprId },
    Pi { binder_type: ExprId, body: ExprId },
    Lambda { binder_type: ExprId, body: ExprId },
    Let {
        binder_type: ExprId,
        val: ExprId,
        body: ExprId,
        nondep: bool,
    },
}

#[derive(Debug, Clone, Copy)]
pub struct ExprNode {
    pub(crate) expr: Expr,
    /// The number of "loose" bound variables, which is the number of bound variables
    /// in an expression which are bound by something above it.
    pub(crate) loose: u16,
    pub(crate) mask: u64,
}

const _: () = assert!(size_of::<ExprNode>() == 32);

impl PartialEq for ExprNode {
    fn eq(&self, o: &Self) -> bool {
        self.expr == o.expr
    }
}
impl Eq for ExprNode {}

impl Hash for ExprNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.expr.hash(state);
    }
}

impl Borrow<Expr> for ExprNode {
    fn borrow(&self) -> &Expr {
        &self.expr
    }
}

pub(crate) const NEAR_VARS: u16 = 63;
pub(crate) const FAR_VARS: u64 = 1 << NEAR_VARS;

#[inline]
pub(crate) fn var_mask(dbj_idx: u16) -> u64 {
    1u64 << dbj_idx.min(NEAR_VARS)
}

#[inline]
pub(crate) fn under_binder(mask: u64, num_loose_bvars: u16) -> u64 {
    let far = if num_loose_bvars > NEAR_VARS + 1 {
        FAR_VARS
    } else {
        0
    };
    (mask >> 1) | far
}

impl ExprNode {
    #[inline]
    fn body_mask(&self) -> u64 {
        under_binder(self.mask, self.loose)
    }

    #[inline]
    pub(crate) fn leaf(expr: Expr) -> Self {
        Self {
            expr,
            loose: 0,
            mask: 0,
        }
    }

    #[inline]
    pub(crate) fn var(dbj_idx: u16) -> Self {
        Self {
            expr: Var { dbj_idx },
            loose: dbj_idx + 1,
            mask: var_mask(dbj_idx),
        }
    }

    #[inline]
    pub(crate) fn app(fun: ExprId, f: &Self, arg: ExprId, a: &Self) -> Self {
        Self {
            expr: App { fun, arg },
            loose: f.loose.max(a.loose),
            mask: f.mask | a.mask,
        }
    }

    #[inline]
    pub(crate) fn pi(binder_type: ExprId, t: &Self, body: ExprId, b: &Self) -> Self {
        Self {
            expr: Pi { binder_type, body },
            loose: t.loose.max(b.loose.saturating_sub(1)),
            mask: t.mask | b.body_mask(),
        }
    }

    #[inline]
    pub(crate) fn lambda(binder_type: ExprId, t: &Self, body: ExprId, b: &Self) -> Self {
        Self {
            expr: Lambda { binder_type, body },
            loose: t.loose.max(b.loose.saturating_sub(1)),
            mask: t.mask | b.body_mask(),
        }
    }

    #[inline]
    pub(crate) fn let_(
        binder_type: ExprId,
        t: &Self,
        val: ExprId,
        v: &Self,
        body: ExprId,
        b: &Self,
        nondep: bool,
    ) -> Self {
        Self {
            expr: Let {
                binder_type,
                val,
                body,
                nondep,
            },
            loose: t.loose.max(v.loose.max(b.loose.saturating_sub(1))),
            mask: t.mask | v.mask | b.body_mask(),
        }
    }

    #[inline]
    pub(crate) fn proj(ty_name: NameId, idx: u16, structure: ExprId, s: &Self) -> Self {
        Self {
            expr: Proj {
                ty_name,
                idx,
                structure,
            },
            loose: s.loose,
            mask: s.mask,
        }
    }
}

impl TcCtx<'_> {
    pub(crate) fn inst_forall_params(
        &mut self,
        mut e: ExprId,
        n: usize,
        all_args: &[ExprId],
    ) -> ExprId {
        for _ in 0..n {
            if let Pi { body, .. } = self.ex(e) {
                e = body;
            } else {
                reject!("type has fewer binders than arguments")
            }
        }
        self.inst_open(e, &all_args[0..n])
    }

    pub(crate) fn lift(&mut self, e: ExprId, cutoff: u16, amount: u16) -> ExprId {
        if amount == 0 || self.loose(e) <= cutoff {
            return e;
        }
        match self.ex(e) {
            Var { dbj_idx } => {
                if dbj_idx >= cutoff {
                    self.mk_var(dbj_idx + amount)
                } else {
                    e
                }
            }
            App { fun, arg } => {
                let fun = self.lift(fun, cutoff, amount);
                let arg = self.lift(arg, cutoff, amount);
                self.mk_app(fun, arg)
            }
            Pi { binder_type, body } => {
                let binder_type = self.lift(binder_type, cutoff, amount);
                let body = self.lift(body, cutoff + 1, amount);
                self.mk_pi(binder_type, body)
            }
            Lambda { binder_type, body } => {
                let binder_type = self.lift(binder_type, cutoff, amount);
                let body = self.lift(body, cutoff + 1, amount);
                self.mk_lambda(binder_type, body)
            }
            Let {
                binder_type,
                val,
                body,
                nondep,
            } => {
                let binder_type = self.lift(binder_type, cutoff, amount);
                let val = self.lift(val, cutoff, amount);
                let body = self.lift(body, cutoff + 1, amount);
                self.mk_let(binder_type, val, body, nondep)
            }
            Proj {
                ty_name,
                idx,
                structure,
            } => {
                let structure = self.lift(structure, cutoff, amount);
                self.mk_proj(ty_name, idx, structure)
            }
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => e,
        }
    }

    pub(crate) fn lower(&mut self, e: ExprId, cutoff: u16, amount: u16) -> ExprId {
        if amount == 0 || self.loose(e) <= cutoff {
            return e;
        }
        match self.ex(e) {
            Var { dbj_idx } => {
                if dbj_idx >= cutoff {
                    assert!(
                        dbj_idx >= cutoff + amount,
                        "lower: reference to a discarded binder"
                    );
                    self.mk_var(dbj_idx - amount)
                } else {
                    e
                }
            }
            App { fun, arg } => {
                let fun = self.lower(fun, cutoff, amount);
                let arg = self.lower(arg, cutoff, amount);
                self.mk_app(fun, arg)
            }
            Pi { binder_type, body } => {
                let binder_type = self.lower(binder_type, cutoff, amount);
                let body = self.lower(body, cutoff + 1, amount);
                self.mk_pi(binder_type, body)
            }
            Lambda { binder_type, body } => {
                let binder_type = self.lower(binder_type, cutoff, amount);
                let body = self.lower(body, cutoff + 1, amount);
                self.mk_lambda(binder_type, body)
            }
            Let {
                binder_type,
                val,
                body,
                nondep,
            } => {
                let binder_type = self.lower(binder_type, cutoff, amount);
                let val = self.lower(val, cutoff, amount);
                let body = self.lower(body, cutoff + 1, amount);
                self.mk_let(binder_type, val, body, nondep)
            }
            Proj {
                ty_name,
                idx,
                structure,
            } => {
                let structure = self.lower(structure, cutoff, amount);
                self.mk_proj(ty_name, idx, structure)
            }
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => e,
        }
    }

    /// Instantiate `e` with the substitutions in `substs`
    pub fn inst(&mut self, e: ExprId, substs: &[ExprId]) -> ExprId {
        self.expr_cache.inst.clear();
        self.inst_aux(e, substs, 0)
    }

    fn inst_aux(&mut self, e: ExprId, substs: &[ExprId], offset: u16) -> ExprId {
        if self.loose(e) <= offset {
            e
        } else if let Some(cached) = self.expr_cache.inst.get(&(e, offset)) {
            cached
        } else {
            let calcd = match self.ex(e) {
                // These expressions should be unreachable since they return `n_loose_bvars() == 0`
                Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => panic!(),
                Var { dbj_idx } => {
                    debug_assert!(dbj_idx >= offset);
                    substs
                        .iter()
                        .rev()
                        .nth((dbj_idx - offset) as usize)
                        .copied()
                        .unwrap_or(e)
                }
                App { fun, arg } => {
                    let fun = self.inst_aux(fun, substs, offset);
                    let arg = self.inst_aux(arg, substs, offset);
                    self.mk_app(fun, arg)
                }
                Pi { binder_type, body } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset);
                    let body = self.inst_aux(body, substs, offset + 1);
                    self.mk_pi(binder_type, body)
                }
                Lambda { binder_type, body } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset);
                    let body = self.inst_aux(body, substs, offset + 1);
                    self.mk_lambda(binder_type, body)
                }
                Let {
                    binder_type,
                    val,
                    body,
                    nondep,
                } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset);
                    let val = self.inst_aux(val, substs, offset);
                    let body = self.inst_aux(body, substs, offset + 1);
                    self.mk_let(binder_type, val, body, nondep)
                }
                Proj {
                    ty_name,
                    idx,
                    structure,
                } => {
                    let structure = self.inst_aux(structure, substs, offset);
                    self.mk_proj(ty_name, idx, structure)
                }
            };
            self.expr_cache.inst.insert((e, offset), calcd);
            calcd
        }
    }

    pub(crate) fn inst_open(&mut self, e: ExprId, substs: &[ExprId]) -> ExprId {
        if substs.iter().all(|&s| self.loose(s) == 0) {
            return self.inst(e, substs);
        }
        self.expr_cache.inst.clear();
        self.inst_open_aux(e, substs, 0)
    }

    fn inst_open_aux(&mut self, e: ExprId, substs: &[ExprId], offset: u16) -> ExprId {
        if self.loose(e) <= offset {
            return e;
        }
        if let Some(cached) = self.expr_cache.inst.get(&(e, offset)) {
            return cached;
        }
        let calcd = match self.ex(e) {
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => panic!(),
            Var { dbj_idx } => match substs
                .iter()
                .rev()
                .nth((dbj_idx - offset) as usize)
                .copied()
            {
                Some(s) => self.lift(s, 0, offset),
                None => e,
            },
            App { fun, arg } => {
                let fun = self.inst_open_aux(fun, substs, offset);
                let arg = self.inst_open_aux(arg, substs, offset);
                self.mk_app(fun, arg)
            }
            Pi { binder_type, body } => {
                let binder_type = self.inst_open_aux(binder_type, substs, offset);
                let body = self.inst_open_aux(body, substs, offset + 1);
                self.mk_pi(binder_type, body)
            }
            Lambda { binder_type, body } => {
                let binder_type = self.inst_open_aux(binder_type, substs, offset);
                let body = self.inst_open_aux(body, substs, offset + 1);
                self.mk_lambda(binder_type, body)
            }
            Let {
                binder_type,
                val,
                body,
                nondep,
            } => {
                let binder_type = self.inst_open_aux(binder_type, substs, offset);
                let val = self.inst_open_aux(val, substs, offset);
                let body = self.inst_open_aux(body, substs, offset + 1);
                self.mk_let(binder_type, val, body, nondep)
            }
            Proj {
                ty_name,
                idx,
                structure,
            } => {
                let structure = self.inst_open_aux(structure, substs, offset);
                self.mk_proj(ty_name, idx, structure)
            }
        };
        self.expr_cache.inst.insert((e, offset), calcd);
        calcd
    }

    fn subst_aux(&mut self, e: ExprId, ks: LevelsId, vs: LevelsId) -> ExprId {
        if let Some(cached) = self.expr_cache.subst.get(&(e, ks, vs)) {
            cached
        } else {
            let r = match self.ex(e) {
                Var { .. } | NatLit { .. } | StringLit { .. } => e,
                Sort { level } => {
                    let level = self.subst_level(level, ks, vs);
                    self.mk_sort(level)
                }
                Const { name, levels } => {
                    let levels = self.subst_levels(levels, ks, vs);
                    self.mk_const(name, levels)
                }
                App { fun, arg } => {
                    let fun = self.subst_aux(fun, ks, vs);
                    let arg = self.subst_aux(arg, ks, vs);
                    self.mk_app(fun, arg)
                }
                Pi { binder_type, body } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_pi(binder_type, body)
                }
                Lambda { binder_type, body } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_lambda(binder_type, body)
                }
                Let {
                    binder_type,
                    val,
                    body,
                    nondep,
                } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let val = self.subst_aux(val, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_let(binder_type, val, body, nondep)
                }
                Proj {
                    ty_name,
                    idx,
                    structure,
                } => {
                    let structure = self.subst_aux(structure, ks, vs);
                    self.mk_proj(ty_name, idx, structure)
                }
            };
            self.expr_cache.subst.insert((e, ks, vs), r);
            r
        }
    }

    pub fn subst_expr_levels(&mut self, e: ExprId, ks: LevelsId, vs: LevelsId) -> ExprId {
        if ks == vs || self.levels(ks).is_empty() {
            ensure_eq!(self.levels(ks).len(), self.levels(vs).len());
            return e;
        }
        if let Some(cached) = self.expr_cache.dsubst.get(&(e, ks, vs)) {
            return cached;
        }
        self.expr_cache.subst.clear();
        ensure_eq!(self.levels(ks).len(), self.levels(vs).len());
        let out = self.subst_aux(e, ks, vs);
        self.expr_cache.dsubst.insert((e, ks, vs), out);
        out
    }

    pub fn foldl_apps(&mut self, mut fun: ExprId, args: impl Iterator<Item = ExprId>) -> ExprId {
        for arg in args {
            fun = self.mk_app(fun, arg);
        }
        fun
    }

    /// Convert a string literal to `String.ofList <| List.cons (Char.ofNat _) .. List.nil`
    pub(crate) fn str_lit_to_constructor(&mut self, s: StrId) -> Option<ExprId> {
        if (!self.export_file.config.string_extension) || (!self.export_file.config.nat_extension) {
            return None;
        }
        let names = self.export_file.name_cache;
        let empty_levels = self.alloc_levels(&[]);
        let tyzero_levels = self.alloc_levels(&[ZERO]);
        // Const(Char, [])
        let c_char = self.mk_const(names.char?, empty_levels);
        // Const(Char.ofNat, [])
        let c_char_of_nat = self.mk_const(names.char_of_nat?, empty_levels);
        // @List.nil.{0} Char
        let c_list_nil_char = {
            let f = self.mk_const(names.list_nil?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        // @List.cons.{0} Char
        let c_list_cons_char = {
            let f = self.mk_const(names.list_cons?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        let mut out = c_list_nil_char;
        let chars: Vec<char> = self.string(s).chars().rev().collect();
        for c in chars {
            let bignum = self.alloc_bignum(BigUint::from(c as u32)).unwrap();
            let bignum = self.mk_nat_lit(bignum).unwrap();
            // Char.ofNat (c as u32)
            let x = self.mk_app(c_char_of_nat, bignum);
            // List.cons (Char.ofNat u32)
            let y = self.mk_app(c_list_cons_char, x);
            // (List.cons (Char.ofNat u32)) xs
            out = self.mk_app(y, out);
        }
        let string_of_list_const = self.mk_const(names.string_of_list?, empty_levels);
        Some(self.mk_app(string_of_list_const, out))
    }

    pub(crate) fn has_nested_name(&self, e: ExprId, nested: NameId) -> bool {
        let mut cache = crate::term::hash::new_fx_hash_map();
        self.has_nested_name_aux(e, nested, &mut cache)
    }

    fn has_nested_name_aux(
        &self,
        e: ExprId,
        nested: NameId,
        cache: &mut FxHashMap<ExprId, bool>,
    ) -> bool {
        if let Some(cached) = cache.get(&e) {
            return *cached;
        }
        let result = match self.ex(e) {
            Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } => false,
            Const { name, .. } => self.get_pfx(name) == nested,
            App { fun, arg } => {
                self.has_nested_name_aux(fun, nested, cache)
                    || self.has_nested_name_aux(arg, nested, cache)
            }
            Pi { binder_type, body } | Lambda { binder_type, body } => {
                self.has_nested_name_aux(binder_type, nested, cache)
                    || self.has_nested_name_aux(body, nested, cache)
            }
            Let {
                binder_type,
                val,
                body,
                ..
            } => {
                self.has_nested_name_aux(binder_type, nested, cache)
                    || self.has_nested_name_aux(val, nested, cache)
                    || self.has_nested_name_aux(body, nested, cache)
            }
            Proj {
                ty_name, structure, ..
            } => {
                self.get_pfx(ty_name) == nested
                    || self.has_nested_name_aux(structure, nested, cache)
            }
        };
        cache.insert(e, result);
        result
    }

    /// Is this expression `Sort(Level::Zero)`?
    pub(crate) fn prop(&mut self) -> ExprId {
        self.mk_sort(ZERO)
    }

    #[inline]
    pub(crate) fn ignores_binder(&self, body: ExprId) -> bool {
        self.mask(body) & 1 == 0
    }

    /// From `f a_0 .. a_N`, return `f`
    pub fn unfold_apps_fun(&self, mut e: ExprId) -> ExprId {
        while let App { fun, .. } = self.ex(e) {
            e = fun;
        }
        e
    }

    /// From `f a_0 .. a_N`, return `(f, [a_0, ..a_N])`
    pub fn unfold_apps(&self, mut e: ExprId) -> (ExprId, Vec<ExprId>) {
        let mut args = Vec::new();
        while let App { fun, arg } = self.ex(e) {
            e = fun;
            args.push(arg);
        }
        args.reverse();
        (e, args)
    }

    /// If this is a const application, return (Const {..}, name, levels, args)
    pub fn unfold_const_apps(&self, e: ExprId) -> Option<(ExprId, NameId, LevelsId, Vec<ExprId>)> {
        let (f, args) = self.unfold_apps(e);
        match self.ex(f) {
            Const { name, levels } => Some((f, name, levels, args)),
            _ => None,
        }
    }

    /// If this is an application of `Const(name, levels)`, return `(name, levels)`
    pub fn try_const_info(&self, e: ExprId) -> Option<(NameId, LevelsId)> {
        match self.ex(e) {
            Const { name, levels } => Some((name, levels)),
            _ => None,
        }
    }

    pub(crate) fn unfold_apps_rev(&self, mut e: ExprId) -> (ExprId, SpineArgs) {
        let mut args = SpineArgs::new();
        while let App { fun, arg } = self.ex(e) {
            args.push(arg);
            e = fun;
        }
        (e, args)
    }

    #[inline(always)]
    pub(crate) fn peel_apps<'b>(
        &self,
        mut e: ExprId,
        buf: &'b mut SpineBuf,
    ) -> Option<(ExprId, &'b [ExprId])> {
        let mut n = 0;
        while let App { fun, arg } = self.ex(e) {
            if n == SPINE {
                return None;
            }
            buf[n].write(arg);
            n += 1;
            e = fun;
        }
        let args = unsafe { slice::from_raw_parts(buf.as_ptr().cast::<ExprId>(), n) };
        Some((e, args))
    }

    pub(crate) fn find_const<F>(&self, e: ExprId, pred: F) -> bool
    where
        F: FnOnce(NameId) -> bool + Copy,
    {
        let mut cache = crate::term::hash::new_fx_hash_map();
        self.find_const_aux(e, pred, &mut cache)
    }

    fn find_const_aux<F>(&self, e: ExprId, pred: F, cache: &mut FxHashMap<ExprId, bool>) -> bool
    where
        F: FnOnce(NameId) -> bool + Copy,
    {
        if let Some(cached) = cache.get(&e) {
            *cached
        } else {
            let r = match self.ex(e) {
                Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } => false,
                Const { name, .. } => pred(name),
                App { fun, arg } => {
                    self.find_const_aux(fun, pred, cache) || self.find_const_aux(arg, pred, cache)
                }
                Pi { binder_type, body } | Lambda { binder_type, body } => {
                    self.find_const_aux(binder_type, pred, cache)
                        || self.find_const_aux(body, pred, cache)
                }
                Let {
                    binder_type,
                    val,
                    body,
                    ..
                } => {
                    self.find_const_aux(binder_type, pred, cache)
                        || self.find_const_aux(val, pred, cache)
                        || self.find_const_aux(body, pred, cache)
                }
                Proj { structure, .. } => self.find_const_aux(structure, pred, cache),
            };
            cache.insert(e, r);
            r
        }
    }

    /// Return the number of leading `Pi` binders on this expression.
    pub(crate) fn pi_telescope_size(&self, mut e: ExprId) -> u16 {
        let mut size = 0u16;
        while let Pi { body, .. } = self.ex(e) {
            size += 1;
            e = body;
        }
        size
    }

    pub fn get_nth_pi_binder(&self, mut e: ExprId, n: usize) -> Option<ExprId> {
        for _ in 0..n {
            match self.ex(e) {
                Pi { body, .. } => {
                    e = body;
                }
                _ => return None,
            }
        }
        match self.ex(e) {
            Pi { binder_type, .. } => Some(binder_type),
            _ => None,
        }
    }

    pub(crate) fn has_loose_bvar(&self, e: ExprId, idx: u16) -> bool {
        if self.loose(e) <= idx {
            return false;
        }
        match self.ex(e) {
            Var { dbj_idx } => dbj_idx == idx,
            App { fun, arg } => self.has_loose_bvar(fun, idx) || self.has_loose_bvar(arg, idx),
            Pi { binder_type, body } | Lambda { binder_type, body } => {
                self.has_loose_bvar(binder_type, idx) || self.has_loose_bvar(body, idx + 1)
            }
            Let {
                binder_type,
                val,
                body,
                ..
            } => {
                self.has_loose_bvar(binder_type, idx)
                    || self.has_loose_bvar(val, idx)
                    || self.has_loose_bvar(body, idx + 1)
            }
            Proj { structure, .. } => self.has_loose_bvar(structure, idx),
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => false,
        }
    }

    pub(crate) fn has_loose_bvar_below(&self, e: ExprId, cutoff: u16) -> bool {
        if cutoff == 0 || self.loose(e) == 0 {
            return false;
        }
        match self.ex(e) {
            Var { dbj_idx } => dbj_idx < cutoff,
            App { fun, arg } => {
                self.has_loose_bvar_below(fun, cutoff) || self.has_loose_bvar_below(arg, cutoff)
            }
            Pi { binder_type, body } | Lambda { binder_type, body } => {
                self.has_loose_bvar_below(binder_type, cutoff)
                    || self.has_loose_bvar_below(body, cutoff + 1)
            }
            Let {
                binder_type,
                val,
                body,
                ..
            } => {
                self.has_loose_bvar_below(binder_type, cutoff)
                    || self.has_loose_bvar_below(val, cutoff)
                    || self.has_loose_bvar_below(body, cutoff + 1)
            }
            Proj { structure, .. } => self.has_loose_bvar_below(structure, cutoff),
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => false,
        }
    }
}
