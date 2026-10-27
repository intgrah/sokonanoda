// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::context::TcCtx;
use crate::term::expr::Expr::{App, Const, Lambda, Let, NatLit, Pi, Proj, Sort, StringLit, Var};
use crate::term::id::{BigId, ExprId, LevelId, LevelsId, NameId, StrId, ZERO};
use crate::term::level::Level;

pub struct DebugPrinter<'x, 't, A> {
    pub(crate) ctx: &'x TcCtx<'t>,
    pub(crate) elem_to_print: A,
}

impl<'x, 't: 'x> TcCtx<'t> {
    pub fn debug_print<A>(&'x self, elem_to_print: A) -> DebugPrinter<'x, 't, A> {
        DebugPrinter {
            ctx: self,
            elem_to_print,
        }
    }
}

impl std::fmt::Debug for DebugPrinter<'_, '_, NameId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.ctx.display(self.elem_to_print))
    }
}

use std::fmt;
impl<'x, 't, A, B> std::fmt::Debug for DebugPrinter<'x, 't, (A, B)>
where
    A: Copy,
    B: Copy,
    DebugPrinter<'x, 't, A>: std::fmt::Debug,
    DebugPrinter<'x, 't, B>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "({:?}, {:?})",
            self.ctx.debug_print(self.elem_to_print.0),
            self.ctx.debug_print(self.elem_to_print.1)
        )
    }
}
impl<'x, 't, A> std::fmt::Debug for DebugPrinter<'x, 't, &[A]>
where
    A: Copy,
    DebugPrinter<'x, 't, A>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(
                self.elem_to_print
                    .iter()
                    .copied()
                    .map(|x| self.ctx.debug_print(x)),
            )
            .finish()
    }
}

impl<'x, 't, A> std::fmt::Debug for DebugPrinter<'x, 't, Vec<A>>
where
    A: Clone,
    DebugPrinter<'x, 't, A>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(
                self.elem_to_print
                    .clone()
                    .into_iter()
                    .map(|x| self.ctx.debug_print(x)),
            )
            .finish()
    }
}
impl<'x, 't, A> std::fmt::Debug for DebugPrinter<'x, 't, std::rc::Rc<A>>
where
    A: Clone,
    DebugPrinter<'x, 't, A>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?}",
            &self.ctx.debug_print(self.elem_to_print.as_ref().clone())
        )
    }
}
impl<'x, 't, A> std::fmt::Debug for DebugPrinter<'x, 't, Option<A>>
where
    A: Copy,
    DebugPrinter<'x, 't, A>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.elem_to_print {
            None => write!(f, "None"),
            Some(ref x) => write!(f, "Some({:?})", self.ctx.debug_print(*x)),
        }
    }
}

impl std::fmt::Debug for DebugPrinter<'_, '_, LevelId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Level::{IMax, Max, Param, Succ, Zero};
        match self.ctx.level(self.elem_to_print) {
            Zero => write!(f, "0"),
            Succ(..) => {
                let (val, n) = self.ctx.level_succs(self.elem_to_print);
                if val == ZERO {
                    write!(f, "{n}")
                } else {
                    write!(f, "{:?} + {}", self.ctx.debug_print(val), n)
                }
            }
            Max(l, r) => {
                write!(f, "max{:?}", self.ctx.debug_print((l, r)))
            }
            IMax(l, r) => {
                write!(f, "imax{:?}", self.ctx.debug_print((l, r)))
            }
            Param(name) => {
                write!(f, "{:?}", self.ctx.debug_print(name))
            }
        }
    }
}

impl std::fmt::Debug for DebugPrinter<'_, '_, ExprId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ctx.ex(self.elem_to_print) {
            Var { dbj_idx } => write!(f, "${dbj_idx}"),
            Sort { level } => write!(f, "Sort({:?})", self.ctx.debug_print(level)),
            Const { name, levels } => write!(
                f,
                "{:?}.{:?}",
                self.ctx.debug_print(name),
                self.ctx.debug_print(levels)
            ),
            App { fun, arg } => write!(
                f,
                "({:?} {:?})",
                self.ctx.debug_print(fun),
                self.ctx.debug_print(arg)
            ),
            Let {
                binder_type: binder,
                val,
                body,
                ..
            } => {
                write!(
                    f,
                    "let _ : {:?} := {:?} in {:?}",
                    self.ctx.debug_print(binder),
                    self.ctx.debug_print(val),
                    self.ctx.debug_print(body)
                )
            }
            Pi { binder_type, body } => {
                write!(
                    f,
                    "Pi (_ : {:?}), {:?}",
                    self.ctx.debug_print(binder_type),
                    self.ctx.debug_print(body)
                )
            }
            Lambda { binder_type, body } => {
                write!(
                    f,
                    "fun (_ : {:?}) => {:?}",
                    self.ctx.debug_print(binder_type),
                    self.ctx.debug_print(body)
                )
            }
            Proj { idx, structure, .. } => {
                write!(f, "%({:?}).{}", self.ctx.debug_print(structure), idx)
            }
            NatLit { lit } => write!(f, "NLit({})", self.ctx.bignum(lit)),
            StringLit { lit } => write!(f, "SLit({})", self.ctx.string(lit)),
        }
    }
}

impl std::fmt::Debug for DebugPrinter<'_, '_, LevelsId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?}",
            self.ctx.debug_print(self.ctx.levels(self.elem_to_print))
        )
    }
}
impl std::fmt::Debug for DebugPrinter<'_, '_, StrId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.ctx.string(self.elem_to_print))
    }
}
impl std::fmt::Debug for DebugPrinter<'_, '_, BigId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.ctx.bignum(self.elem_to_print))
    }
}

impl std::fmt::Debug for DebugPrinter<'_, '_, &crate::checker::env::DeclarInfo> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeclarInfo")
            .field("name", &self.ctx.debug_print(self.elem_to_print.name))
            .field("ty", &self.ctx.debug_print(self.elem_to_print.ty))
            .field("uparams", &self.ctx.debug_print(self.elem_to_print.uparams))
            .finish()
    }
}

impl std::fmt::Debug for DebugPrinter<'_, '_, crate::checker::env::RecRule> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RecRule")
            .field(
                "ctor_name",
                &self.ctx.debug_print(self.elem_to_print.ctor_name),
            )
            .field(
                "ctor_telescope_size_wo_params",
                &self.elem_to_print.ctor_telescope_size_wo_params,
            )
            .field("val", &self.ctx.debug_print(self.elem_to_print.val))
            .finish()
    }
}

impl std::fmt::Debug for DebugPrinter<'_, '_, crate::checker::env::ReducibilityHint> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.elem_to_print)
    }
}
