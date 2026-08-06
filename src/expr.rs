//! Implementation of Lean expressions
use crate::util::{BigUintPtr, ExprPtr, FxHashMap, LevelPtr, LevelsPtr, NamePtr, StringPtr, TcCtx};
use num_bigint::BigUint;
use Expr::*;
use serde::Deserialize;

pub(crate) const VAR_HASH: u64 = 281;
pub(crate) const SORT_HASH: u64 = 563;
pub(crate) const CONST_HASH: u64 = 1129;
pub(crate) const PROJ_HASH: u64 = 17;
pub(crate) const LAMBDA_HASH: u64 = 431;
pub(crate) const LET_HASH: u64 = 241;
pub(crate) const PI_HASH: u64 = 719;
pub(crate) const APP_HASH: u64 = 233;
pub(crate) const STRING_LIT_HASH: u64 = 1493;
pub(crate) const NAT_LIT_HASH: u64 = 1583;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr<'a> {
    /// A string literal with a pointer to a utf-8 string.
    StringLit {
        hash: u64,
        ptr: StringPtr<'a>,
    },
    /// A nat literal, holds a pointer to an arbitrary precision bignum.
    NatLit {
        hash: u64,
        ptr: BigUintPtr<'a>,
    },
    Proj {
        hash: u64,
        /// The name of the structure being projected. E.g. `Prod` if this is
        /// projection 0 of `Prod.mk ..`
        ty_name: NamePtr<'a>,
        /// The 0-based position of the constructor argument, not considering the
        /// parameters. For some struct Foo A B, and a constructor Foo.mk A B p q r s,
        /// `q` will have idx 1.
        idx: u16,
        structure: ExprPtr<'a>,
        fv_mask: u64,
    },
    /// A bound variable represented by a deBruijn index.
    Var {
        hash: u64,
        dbj_idx: u16,
    },
    Sort {
        hash: u64,
        level: LevelPtr<'a>,
    },
    Const {
        hash: u64,
        name: NamePtr<'a>,
        levels: LevelsPtr<'a>,
    },
    App {
        hash: u64,
        fun: ExprPtr<'a>,
        arg: ExprPtr<'a>,
        fv_mask: u64,
    },
    Pi {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: ExprPtr<'a>,
        fv_mask: u64,
    },
    Lambda {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: ExprPtr<'a>,
        fv_mask: u64,
    },
    Let {
        hash: u64,
        data: &'a LetData<'a>,
        fv_mask: u64,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LetData<'a> {
    pub binder_name: NamePtr<'a>,
    pub binder_type: ExprPtr<'a>,
    pub val: ExprPtr<'a>,
    pub body: ExprPtr<'a>,
    pub nondep: bool,
}

impl<'a> Expr<'a> {
    pub(crate) fn get_hash(&self) -> u64 {
        match self {
            Var { hash, .. }
            | Sort { hash, .. }
            | Const { hash, .. }
            | App { hash, .. }
            | Pi { hash, .. }
            | Lambda { hash, .. }
            | Let { hash, .. }
            | StringLit { hash, .. }
            | NatLit { hash, .. }
            | Proj { hash, .. } => *hash,
        }
    }
}
impl<'a> std::hash::Hash for Expr<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

impl<'a> crate::util::RawHash for Expr<'a> {
    #[inline]
    fn raw_hash(&self) -> u64 { self.get_hash() }
}

/// The style of this binder (in Lean's vernacular, the brackets used to write it).
/// `(_ : _)` for default, `{_ : _}` for implicit, `{{_ : _}}` for strict implicit,
/// and `[_ : _]` for instance implicit.
///
/// These are only used by the pretty printer, and do not change the behavior of
/// type checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Deserialize)]
pub enum BinderStyle {
    #[serde(rename = "default")]
    Default,
    #[serde(rename = "implicit")]
    Implicit,
    #[serde(rename = "strictImplicit")]
    StrictImplicit,
    #[serde(rename = "instImplicit")]
    InstanceImplicit,
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub(crate) fn inst_forall_params(&mut self, mut e: ExprPtr<'t>, n: usize, all_args: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        for _ in 0..n {
            if let Pi { body, .. } = self.read_expr(e) {
                e = body
            } else {
                panic!()
            }
        }
        self.inst_open(e, &all_args[0..n])
    }

    pub(crate) fn lift(&mut self, e: ExprPtr<'t>, cutoff: u16, amount: u16) -> ExprPtr<'t> {
        if amount == 0 || self.num_loose_bvars(e) <= cutoff {
            return e
        }
        match self.read_expr(e) {
            Var { dbj_idx, .. } =>
                if dbj_idx >= cutoff {
                    self.mk_var(dbj_idx + amount)
                } else {
                    e
                },
            App { fun, arg, .. } => {
                let fun = self.lift(fun, cutoff, amount);
                let arg = self.lift(arg, cutoff, amount);
                self.mk_app(fun, arg)
            }
            Pi { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.lift(binder_type, cutoff, amount);
                let body = self.lift(body, cutoff + 1, amount);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.lift(binder_type, cutoff, amount);
                let body = self.lift(body, cutoff + 1, amount);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            Let { data, .. } => {
                    let crate::expr::LetData { binder_name, binder_type, val, body, nondep } = *data;
                let binder_type = self.lift(binder_type, cutoff, amount);
                let val = self.lift(val, cutoff, amount);
                let body = self.lift(body, cutoff + 1, amount);
                self.mk_let(binder_name, binder_type, val, body, nondep)
            }
            Proj { ty_name, idx, structure, .. } => {
                let structure = self.lift(structure, cutoff, amount);
                self.mk_proj(ty_name, idx, structure)
            }
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => e,
        }
    }

    pub(crate) fn lower(&mut self, e: ExprPtr<'t>, cutoff: u16, amount: u16) -> ExprPtr<'t> {
        if amount == 0 || self.num_loose_bvars(e) <= cutoff {
            return e
        }
        match self.read_expr(e) {
            Var { dbj_idx, .. } =>
                if dbj_idx >= cutoff {
                    assert!(dbj_idx >= cutoff + amount, "lower: reference to a discarded binder");
                    self.mk_var(dbj_idx - amount)
                } else {
                    e
                },
            App { fun, arg, .. } => {
                let fun = self.lower(fun, cutoff, amount);
                let arg = self.lower(arg, cutoff, amount);
                self.mk_app(fun, arg)
            }
            Pi { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.lower(binder_type, cutoff, amount);
                let body = self.lower(body, cutoff + 1, amount);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.lower(binder_type, cutoff, amount);
                let body = self.lower(body, cutoff + 1, amount);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            Let { data, .. } => {
                    let crate::expr::LetData { binder_name, binder_type, val, body, nondep } = *data;
                let binder_type = self.lower(binder_type, cutoff, amount);
                let val = self.lower(val, cutoff, amount);
                let body = self.lower(body, cutoff + 1, amount);
                self.mk_let(binder_name, binder_type, val, body, nondep)
            }
            Proj { ty_name, idx, structure, .. } => {
                let structure = self.lower(structure, cutoff, amount);
                self.mk_proj(ty_name, idx, structure)
            }
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => e,
        }
    }

    /// Instantiate `e` with the substitutions in `substs`
    pub fn inst(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        self.expr_cache.inst_cache.clear();
        self.inst_aux(e, substs, 0)
    }

    fn inst_aux(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>], offset: u16) -> ExprPtr<'t> {
        if self.num_loose_bvars(e) <= offset {
            e
        } else if let Some(cached) = self.expr_cache.inst_cache.get(&(e, offset)) {
            *cached
        } else {
            let calcd = match self.read_expr(e) {
                // These expressions should be unreachable since they return `n_loose_bvars() == 0`
                Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => panic!(),
                Var { dbj_idx, .. } => {
                    debug_assert!(dbj_idx >= offset);
                    substs.iter().rev().nth((dbj_idx - offset) as usize).copied().unwrap_or(e)
                }
                App { fun, arg, .. } => {
                    let fun = self.inst_aux(fun, substs, offset);
                    let arg = self.inst_aux(arg, substs, offset);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset);
                    let body = self.inst_aux(body, substs, offset + 1);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset);
                    let body = self.inst_aux(body, substs, offset + 1);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { data, .. } => {
                    let crate::expr::LetData { binder_name, binder_type, val, body, nondep } = *data;
                    let binder_type = self.inst_aux(binder_type, substs, offset);
                    let val = self.inst_aux(val, substs, offset);
                    let body = self.inst_aux(body, substs, offset + 1);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.inst_aux(structure, substs, offset);
                    self.mk_proj(ty_name, idx, structure)
                }
            };
            self.expr_cache.inst_cache.insert((e, offset), calcd);
            calcd
        }
    }

    pub(crate) fn inst_open(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        if substs.iter().all(|s| self.num_loose_bvars(*s) == 0) {
            return self.inst(e, substs)
        }
        self.expr_cache.inst_cache.clear();
        self.inst_open_aux(e, substs, 0)
    }

    fn inst_open_aux(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>], offset: u16) -> ExprPtr<'t> {
        if self.num_loose_bvars(e) <= offset {
            return e
        }
        if let Some(cached) = self.expr_cache.inst_cache.get(&(e, offset)) {
            return *cached
        }
        let calcd = match self.read_expr(e) {
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => panic!(),
            Var { dbj_idx, .. } => match substs.iter().rev().nth((dbj_idx - offset) as usize).copied() {
                Some(s) => self.lift(s, 0, offset),
                None => e,
            },
            App { fun, arg, .. } => {
                let fun = self.inst_open_aux(fun, substs, offset);
                let arg = self.inst_open_aux(arg, substs, offset);
                self.mk_app(fun, arg)
            }
            Pi { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.inst_open_aux(binder_type, substs, offset);
                let body = self.inst_open_aux(body, substs, offset + 1);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.inst_open_aux(binder_type, substs, offset);
                let body = self.inst_open_aux(body, substs, offset + 1);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            Let { data, .. } => {
                    let crate::expr::LetData { binder_name, binder_type, val, body, nondep } = *data;
                let binder_type = self.inst_open_aux(binder_type, substs, offset);
                let val = self.inst_open_aux(val, substs, offset);
                let body = self.inst_open_aux(body, substs, offset + 1);
                self.mk_let(binder_name, binder_type, val, body, nondep)
            }
            Proj { ty_name, idx, structure, .. } => {
                let structure = self.inst_open_aux(structure, substs, offset);
                self.mk_proj(ty_name, idx, structure)
            }
        };
        self.expr_cache.inst_cache.insert((e, offset), calcd);
        calcd
    }

    fn subst_aux(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> ExprPtr<'t> {
        if let Some(cached) = self.expr_cache.subst_cache.get(&(e, ks, vs)) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | NatLit { .. } | StringLit { .. } => e,
                Sort { level, .. } => {
                    let level = self.subst_level(level, ks, vs);
                    self.mk_sort(level)
                }
                Const { name, levels, .. } => {
                    let levels = self.subst_levels(levels, ks, vs);
                    self.mk_const(name, levels)
                }
                App { fun, arg, .. } => {
                    let fun = self.subst_aux(fun, ks, vs);
                    let arg = self.subst_aux(arg, ks, vs);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { data, .. } => {
                    let crate::expr::LetData { binder_name, binder_type, val, body, nondep } = *data;
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let val = self.subst_aux(val, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.subst_aux(structure, ks, vs);
                    self.mk_proj(ty_name, idx, structure)
                }
            };
            self.expr_cache.subst_cache.insert((e, ks, vs), r);
            r
        }
    }

    pub fn subst_expr_levels(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> ExprPtr<'t> {
        if ks == vs || self.read_levels(ks).is_empty() {
            assert_eq!(self.read_levels(ks).len(), self.read_levels(vs).len());
            return e;
        }
        if let Some(cached) = self.expr_cache.dsubst_cache.get(&(e, ks, vs)).copied() {
            return cached
        }
        self.expr_cache.subst_cache.clear();
        assert_eq!(self.read_levels(ks).len(), self.read_levels(vs).len());
        let out = self.subst_aux(e, ks, vs);
        self.expr_cache.dsubst_cache.insert((e, ks, vs), out);
        out
    }


    pub fn num_args(&self, e: ExprPtr<'t>) -> usize {
        let (mut cursor, mut num_args) = (e, 0);
        while let App { fun, .. } = self.read_expr(cursor) {
            cursor = fun;
            num_args += 1;
        }
        num_args
    }

    /// From `f a_0 .. a_N`, return `f`
    pub fn unfold_apps_fun(&self, mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        while let App { fun, .. } = self.read_expr(e) {
            e = fun;
        }
        e
    }

    /// From `f a_0 .. a_N`, return `(f, [a_0, ..a_N])`
    pub fn unfold_apps<'b>(
        &self,
        arena: &'b bumpalo::Bump,
        mut e: ExprPtr<'t>,
    ) -> (ExprPtr<'t>, bumpalo::collections::Vec<'b, ExprPtr<'t>>) {
        let mut args = bumpalo::collections::Vec::new_in(arena);
        loop {
            match self.read_expr(e) {
                App { fun, arg, .. } => {
                    e = fun;
                    args.push(arg);
                },
                _ => break
            }
        }
        args.reverse();
        (e, args)
    }
    
    /// If this is a const application, return (Const {..}, name, levels, args)
    pub fn unfold_const_apps<'b>(
        &self,
        arena: &'b bumpalo::Bump,
        e: ExprPtr<'t>,
    ) -> Option<(ExprPtr<'t>, NamePtr<'t>, LevelsPtr<'t>, bumpalo::collections::Vec<'b, ExprPtr<'t>>)> {
        let (f, args) = self.unfold_apps(arena, e);
        match self.read_expr(f) {
            Const { name, levels, .. } => Some((f, name, levels, args)),
            _ => None,
        }
    }
    /// If this is an application of `Const(name, levels)`, return `(name, levels)`
    pub fn try_const_info(&self, e: ExprPtr<'t>) -> Option<(NamePtr<'t>, LevelsPtr<'t>)> {
        match self.read_expr(e) {
            Const { name, levels, .. } => Some((name, levels)),
            _ => None,
        }
    }

    pub(crate) fn unfold_apps_stack<'b>(
        &self,
        arena: &'b bumpalo::Bump,
        mut e: ExprPtr<'t>,
    ) -> (ExprPtr<'t>, bumpalo::collections::Vec<'b, ExprPtr<'t>>) {
        let mut args = bumpalo::collections::Vec::new_in(arena);
        while let App { fun, arg, .. } = self.read_expr(e) {
            args.push(arg);
            e = fun;
        }
        (e, args)
    }

    pub fn foldl_apps(&mut self, mut fun: ExprPtr<'t>, args: impl Iterator<Item = ExprPtr<'t>>) -> ExprPtr<'t> {
        for arg in args {
            fun = self.mk_app(fun, arg);
        }
        fun
    }

    /// Convert a string literal to `String.ofList <| List.cons (Char.ofNat _) .. List.nil`
    pub(crate) fn str_lit_to_constructor(&mut self, s: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        if (!self.export_file.config.string_extension) || (!self.export_file.config.nat_extension) {
            return None
        }
        let zero = self.zero();
        let empty_levels = self.alloc_levels_slice(&[]);
        let tyzero_levels = self.alloc_levels_slice(&[zero]);
        // Const(Char, [])
        let c_char = self.mk_const(self.export_file.name_cache.char?, empty_levels);
        // Const(Char.ofNat, [])
        let c_char_of_nat = self.mk_const(self.export_file.name_cache.char_of_nat?, empty_levels);
        // @List.nil.{0} Char
        let c_list_nil_char = {
            let f = self.mk_const(self.export_file.name_cache.list_nil?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        // @List.cons.{0} Char
        let c_list_cons_char = {
            let f = self.mk_const(self.export_file.name_cache.list_cons?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        let mut out = c_list_nil_char;
        for c in self.read_string(s).clone().chars().rev() {
            let bignum = self.alloc_bignum(BigUint::from(c as u32)).unwrap();
            let bignum = self.mk_nat_lit(bignum).unwrap();
            // Char.ofNat (c as u32)
            let x = self.mk_app(c_char_of_nat, bignum);
            // List.cons (Char.ofNat u32)
            let y = self.mk_app(c_list_cons_char, x);
            // (List.cons (Char.ofNat u32)) xs
            out = self.mk_app(y, out);
        }
        let string_of_list_const = self.mk_const(self.export_file.name_cache.string_of_list?, empty_levels);
        Some(self.mk_app(string_of_list_const, out))
    }



    pub(crate) fn find_const<F>(&self, e: ExprPtr<'t>, pred: F) -> bool
    where
        F: FnOnce(NamePtr<'t>) -> bool + Copy, {
        let mut cache = crate::util::new_fx_hash_map();
        self.find_const_aux(e, pred, &mut cache)
    }

    fn find_const_aux<F>(&self, e: ExprPtr<'t>, pred: F, cache: &mut FxHashMap<ExprPtr<'t>, bool>) -> bool
    where
        F: FnOnce(NamePtr<'t>) -> bool + Copy, {
        if let Some(cached) = cache.get(&e) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } => false,
                Const { name, .. } => pred(name),
                App { fun, arg, .. } => self.find_const_aux(fun, pred, cache) || self.find_const_aux(arg, pred, cache),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } =>
                    self.find_const_aux(binder_type, pred, cache) || self.find_const_aux(body, pred, cache),
                Let { data: &crate::expr::LetData { binder_type, val, body, .. }, .. } =>
                    self.find_const_aux(binder_type, pred, cache)
                        || self.find_const_aux(val, pred, cache)
                        || self.find_const_aux(body, pred, cache),
                Proj { structure, .. } => self.find_const_aux(structure, pred, cache),
            };
            cache.insert(e, r);
            r
        }
    }

    /// Return the number of leading `Pi` binders on this expression.
    pub(crate) fn pi_telescope_size(&self, mut e: ExprPtr<'t>) -> u16 {
        let mut size = 0u16;
        while let Pi { body, .. } = self.read_expr(e) {
            size += 1;
            e = body;
        }
        size
    }

    /// Is this expression `Sort(Level::Zero)`?
    pub(crate) fn prop(&mut self) -> ExprPtr<'t> { self.mk_sort(self.zero()) }

    pub fn get_nth_pi_binder(&self, mut e: ExprPtr<'t>, n: usize) -> Option<ExprPtr<'t>> {
        for _ in 0.. n {
            match self.read_expr(e) {
                Pi {body, ..} => { e = body; },
                _ => return None
            }
        }
        match self.read_expr(e) {
            Pi {binder_type, ..} => Some(binder_type),
            _ => None
        }
    }

    /// Get the name of the inductive type which is the major premise for this recursor
    /// by finding the correct binder in the recursor's type.
    pub fn get_major_induct(&self, rec: &crate::env::RecursorData<'t>) -> Option<NamePtr<'t>> {
        match self.get_nth_pi_binder(rec.info.ty, rec.major_idx()).map(|x| self.read_expr(self.unfold_apps_fun(x))) {
            Some(Const {name, ..}) => Some(name),
            _ => None
        }
    }
    
    /// The number of "loose" bound variables, which is the number of bound variables
    /// in an expression which are boudn by something above it.
    pub(crate) fn num_loose_bvars(&self, e: ExprPtr<'t>) -> u16 { e.num_loose_bvars() }

    pub(crate) fn has_loose_bvar(&self, e: ExprPtr<'t>, idx: u16) -> bool {
        if e.num_loose_bvars() <= idx {
            return false
        }
        match self.read_expr(e) {
            Var { dbj_idx, .. } => dbj_idx == idx,
            App { fun, arg, .. } => self.has_loose_bvar(fun, idx) || self.has_loose_bvar(arg, idx),
            Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } =>
                self.has_loose_bvar(binder_type, idx) || self.has_loose_bvar(body, idx + 1),
            Let { data: &crate::expr::LetData { binder_type, val, body, .. }, .. } =>
                self.has_loose_bvar(binder_type, idx)
                    || self.has_loose_bvar(val, idx)
                    || self.has_loose_bvar(body, idx + 1),
            Proj { structure, .. } => self.has_loose_bvar(structure, idx),
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => false,
        }
    }

    pub(crate) fn has_loose_bvar_below(&self, e: ExprPtr<'t>, cutoff: u16) -> bool {
        if cutoff == 0 || e.num_loose_bvars() == 0 {
            return false
        }
        match self.read_expr(e) {
            Var { dbj_idx, .. } => dbj_idx < cutoff,
            App { fun, arg, .. } => self.has_loose_bvar_below(fun, cutoff) || self.has_loose_bvar_below(arg, cutoff),
            Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } =>
                self.has_loose_bvar_below(binder_type, cutoff) || self.has_loose_bvar_below(body, cutoff + 1),
            Let { data: &crate::expr::LetData { binder_type, val, body, .. }, .. } =>
                self.has_loose_bvar_below(binder_type, cutoff)
                    || self.has_loose_bvar_below(val, cutoff)
                    || self.has_loose_bvar_below(body, cutoff + 1),
            Proj { structure, .. } => self.has_loose_bvar_below(structure, cutoff),
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => false,
        }
    }
}

#[inline]
pub(crate) fn child_mask(e: ExprPtr<'_>) -> u64 {
    let k = e.num_loose_bvars();
    if k == 0 || k > 64 {
        0
    } else {
        e.as_ref().fv_mask()
    }
}

#[inline]
pub(crate) fn body_mask(body: ExprPtr<'_>) -> u64 {
    let k = body.num_loose_bvars();
    if k == 0 {
        0
    } else if k <= 64 {
        body.as_ref().fv_mask() >> 1
    } else {
        u64::MAX
    }
}

impl<'t> Expr<'t> {
    /// The number of "loose" bound variables, which is the number of bound variables
    /// in an expression which are boudn by something above it.
    pub(crate) fn num_loose_bvars(&self) -> u16 {
        match self {
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => 0,
            Var { dbj_idx, .. } => dbj_idx + 1,
            App { fun, arg, .. } => fun.num_loose_bvars().max(arg.num_loose_bvars()),
            Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } =>
                binder_type.num_loose_bvars().max(body.num_loose_bvars().saturating_sub(1)),
            Let { data, .. } => data
                .binder_type
                .num_loose_bvars()
                .max(data.val.num_loose_bvars().max(data.body.num_loose_bvars().saturating_sub(1))),
            Proj { structure, .. } => structure.num_loose_bvars(),
        }
    }

    #[inline]
    pub(crate) fn fv_mask(&self) -> u64 {
        match self {
            Var { dbj_idx, .. } =>
                if *dbj_idx < 64 {
                    1u64 << dbj_idx
                } else {
                    0
                },
            App { fv_mask, .. }
            | Pi { fv_mask, .. }
            | Lambda { fv_mask, .. }
            | Let { fv_mask, .. }
            | Proj { fv_mask, .. } => *fv_mask,
            Sort { .. } | Const { .. } | StringLit { .. } | NatLit { .. } => 0,
        }
    }

}


const _: () = assert!(std::mem::size_of::<Expr<'static>>() == 48);
