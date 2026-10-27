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
    StringLit {
        lit: StrId,
    },
    /// A nat literal, an arbitrary precision bignum.
    NatLit {
        lit: BigId,
    },
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
    Var {
        dbj_idx: u16,
    },
    Sort {
        level: LevelId,
    },
    Const {
        name: NameId,
        levels: LevelsId,
    },
    App {
        fun: ExprId,
        arg: ExprId,
    },
    Pi {
        binder_type: ExprId,
        body: ExprId,
    },
    Lambda {
        binder_type: ExprId,
        body: ExprId,
    },
    Let {
        binder_type: ExprId,
        val: ExprId,
        body: ExprId,
        nondep: bool,
    },
}

impl Expr {
    #[inline]
    pub(crate) fn map_children(self, mut f: impl FnMut(ExprId, u16) -> ExprId) -> Self {
        match self {
            App { fun, arg } => App {
                fun: f(fun, 0),
                arg: f(arg, 0),
            },
            Pi { binder_type, body } => Pi {
                binder_type: f(binder_type, 0),
                body: f(body, 1),
            },
            Lambda { binder_type, body } => Lambda {
                binder_type: f(binder_type, 0),
                body: f(body, 1),
            },
            Let {
                binder_type,
                val,
                body,
                nondep,
            } => Let {
                binder_type: f(binder_type, 0),
                val: f(val, 0),
                body: f(body, 1),
                nondep,
            },
            Proj {
                ty_name,
                idx,
                structure,
            } => Proj {
                ty_name,
                idx,
                structure: f(structure, 0),
            },
            Var { .. } | Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => self,
        }
    }

    #[inline]
    pub(crate) fn any_child(self, mut f: impl FnMut(ExprId, u16) -> bool) -> bool {
        match self {
            App { fun, arg } => f(fun, 0) || f(arg, 0),
            Pi { binder_type, body } | Lambda { binder_type, body } => {
                f(binder_type, 0) || f(body, 1)
            }
            Let {
                binder_type,
                val,
                body,
                ..
            } => f(binder_type, 0) || f(val, 0) || f(body, 1),
            Proj { structure, .. } => f(structure, 0),
            Var { .. } | Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => false,
        }
    }

    pub(crate) fn for_each_child(self, mut f: impl FnMut(ExprId, u16)) {
        self.any_child(|child, binders| {
            f(child, binders);
            false
        });
    }
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
    #[inline]
    pub(crate) fn rebuild_expr(&mut self, original: ExprId, expr: Expr) -> ExprId {
        match expr {
            App { fun, arg } => self.mk_app(fun, arg),
            Pi { binder_type, body } => self.mk_pi(binder_type, body),
            Lambda { binder_type, body } => self.mk_lambda(binder_type, body),
            Let {
                binder_type,
                val,
                body,
                nondep,
            } => self.mk_let(binder_type, val, body, nondep),
            Proj {
                ty_name,
                idx,
                structure,
            } => self.mk_proj(ty_name, idx, structure),
            Var { .. } | Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => original,
        }
    }

    #[inline]
    fn map_expr_children(
        &mut self,
        e: ExprId,
        mut f: impl FnMut(&mut Self, ExprId, u16) -> ExprId,
    ) -> ExprId {
        let expr = self
            .ex(e)
            .map_children(|child, binders| f(self, child, binders));
        self.rebuild_expr(e, expr)
    }

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
            Var { dbj_idx } => self.mk_var(dbj_idx + amount),
            _ => self.map_expr_children(e, |ctx, child, binders| {
                ctx.lift(child, cutoff + binders, amount)
            }),
        }
    }

    pub(crate) fn lower(&mut self, e: ExprId, cutoff: u16, amount: u16) -> ExprId {
        if amount == 0 || self.loose(e) <= cutoff {
            return e;
        }
        match self.ex(e) {
            Var { dbj_idx } => {
                assert!(
                    dbj_idx >= cutoff + amount,
                    "lower: reference to a discarded binder"
                );
                self.mk_var(dbj_idx - amount)
            }
            _ => self.map_expr_children(e, |ctx, child, binders| {
                ctx.lower(child, cutoff + binders, amount)
            }),
        }
    }

    /// Instantiate `e` with the substitutions in `substs`
    pub fn inst(&mut self, e: ExprId, substs: &[ExprId]) -> ExprId {
        self.expr_cache.inst.clear();
        self.inst_aux::<false>(e, substs, 0)
    }

    fn inst_aux<const OPEN: bool>(&mut self, e: ExprId, substs: &[ExprId], offset: u16) -> ExprId {
        if self.loose(e) <= offset {
            return e;
        }
        if let Some(cached) = self.expr_cache.inst.get(&(e, offset)) {
            return cached;
        }
        let calcd = match self.ex(e) {
            Var { dbj_idx } => {
                debug_assert!(dbj_idx >= offset);
                match substs
                    .iter()
                    .rev()
                    .nth((dbj_idx - offset) as usize)
                    .copied()
                {
                    Some(s) if OPEN => self.lift(s, 0, offset),
                    Some(s) => s,
                    None => e,
                }
            }
            _ => self.map_expr_children(e, |ctx, child, binders| {
                ctx.inst_aux::<OPEN>(child, substs, offset + binders)
            }),
        };
        self.expr_cache.inst.insert((e, offset), calcd);
        calcd
    }

    pub(crate) fn inst_open(&mut self, e: ExprId, substs: &[ExprId]) -> ExprId {
        if substs.iter().all(|&s| self.loose(s) == 0) {
            return self.inst(e, substs);
        }
        self.expr_cache.inst.clear();
        self.inst_aux::<true>(e, substs, 0)
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
                _ => self.map_expr_children(e, |ctx, child, _| ctx.subst_aux(child, ks, vs)),
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
            let expr = self.ex(e);
            let r = match expr {
                Const { name, .. } => pred(name),
                _ => expr.any_child(|child, _| self.find_const_aux(child, pred, cache)),
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
        let expr = self.ex(e);
        match expr {
            Var { dbj_idx } => dbj_idx == idx,
            _ => expr.any_child(|child, binders| self.has_loose_bvar(child, idx + binders)),
        }
    }

    pub(crate) fn has_loose_bvar_below(&self, e: ExprId, cutoff: u16) -> bool {
        if cutoff == 0 || self.loose(e) == 0 {
            return false;
        }
        let expr = self.ex(e);
        match expr {
            Var { dbj_idx } => dbj_idx < cutoff,
            _ => {
                expr.any_child(|child, binders| self.has_loose_bvar_below(child, cutoff + binders))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::config::Config;
    use crate::frontend::parser::parse_export_file;
    use std::io;

    #[test]
    fn instantiation_does_not_capture_open_substitutions() {
        let export = parse_export_file(io::empty(), Config::default(), 0).unwrap();
        export.with_ctx(|ctx, _, _| {
            let [v0, v1, v2, v3, v4, v5] = [0, 1, 2, 3, 4, 5].map(|i| ctx.mk_var(i));
            let name = ctx.str1("Structure");
            let val = ctx.mk_proj(name, 1, v1);
            let body = ctx.mk_app(v2, v0);
            let body = ctx.mk_let(v1, val, body, false);
            let expr = ctx.mk_lambda(v0, body);

            let val = ctx.mk_proj(name, 1, v4);
            let body = ctx.mk_app(v5, v0);
            let body = ctx.mk_let(v4, val, body, false);
            let expected = ctx.mk_lambda(v3, body);
            assert_eq!(ctx.inst_open(expr, &[v3]), expected);

            let prop = ctx.prop();
            let val = ctx.mk_proj(name, 1, prop);
            let body = ctx.mk_app(prop, v0);
            let body = ctx.mk_let(prop, val, body, false);
            let expected = ctx.mk_lambda(prop, body);
            assert_eq!(ctx.inst(expr, &[prop]), expected);
            assert_eq!(ctx.inst_open(expr, &[prop]), expected);
        });
    }

    #[test]
    fn shifting_respects_let_value_and_binder_scopes() {
        let export = parse_export_file(io::empty(), Config::default(), 0).unwrap();
        export.with_ctx(|ctx, _, _| {
            let [v0, v1, v2, v3, v4, v5] = [0, 1, 2, 3, 4, 5].map(|i| ctx.mk_var(i));
            let val = ctx.mk_app(v0, v1);
            let body = ctx.mk_app(v0, v3);
            let body = ctx.mk_pi(v2, body);
            let expr = ctx.mk_let(v1, val, body, false);

            let val = ctx.mk_app(v0, v3);
            let body = ctx.mk_app(v0, v5);
            let body = ctx.mk_pi(v4, body);
            let expected = ctx.mk_let(v3, val, body, false);
            assert_eq!(ctx.lift(expr, 1, 2), expected);
            assert_eq!(ctx.lower(expected, 1, 2), expr);
            assert!(ctx.has_loose_bvar(expected, 0));
            assert!(ctx.has_loose_bvar(expected, 3));
            assert!(!ctx.has_loose_bvar(expected, 1));
        });
    }
}
