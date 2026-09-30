use crate::checker::context::TcCtx;
use crate::term::expr::Expr::{App, Const, Lambda, Let, NatLit, Pi, Proj, Sort, StringLit, Var};
use crate::term::level::Level;
use crate::term::name::Name;
use crate::term::ptr::{ExprPtr, LevelPtr, NamePtr};

pub struct DebugPrinter<'x, 't, 'p, A> {
    pub(crate) ctx: &'x TcCtx<'t, 'p>,
    pub(crate) elem_to_print: A,
}

impl<'x, 't: 'x, 'p: 't> TcCtx<'t, 'p> {
    pub fn debug_print<A>(&'x self, elem_to_print: A) -> DebugPrinter<'x, 't, 'p, A> {
        DebugPrinter {
            ctx: self,
            elem_to_print,
        }
    }
}

impl<'t> std::fmt::Debug for DebugPrinter<'_, 't, '_, NamePtr<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Name::{Anon, Num, Str};
        match self.elem_to_print.as_ref().kind {
            Anon => Ok(()),
            Str(pfx, sfx, _) => {
                let sfx = sfx.as_ref();
                match pfx.as_ref().kind {
                    Anon => write!(f, "{sfx}"),
                    _ => write!(f, "{:?}.{}", self.ctx.debug_print(pfx), sfx),
                }
            }
            Num(pfx, sfx, _) => match pfx.as_ref().kind {
                Anon => write!(f, "{sfx}"),
                _ => write!(f, "{:?}.{}", self.ctx.debug_print(pfx), sfx),
            },
        }
    }
}

use std::fmt;
impl<'x, 't, 'p, A, B> std::fmt::Debug for DebugPrinter<'x, 't, 'p, (A, B)>
where
    A: Copy,
    B: Copy,
    DebugPrinter<'x, 't, 'p, A>: std::fmt::Debug,
    DebugPrinter<'x, 't, 'p, B>: std::fmt::Debug,
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
impl<'x, 't, 'p, A> std::fmt::Debug for DebugPrinter<'x, 't, 'p, &[A]>
where
    A: Copy,
    DebugPrinter<'x, 't, 'p, A>: std::fmt::Debug,
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

impl<'x, 't, 'p, A> std::fmt::Debug for DebugPrinter<'x, 't, 'p, Vec<A>>
where
    A: Clone,
    DebugPrinter<'x, 't, 'p, A>: std::fmt::Debug,
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
impl<'x, 't, 'p, A> std::fmt::Debug for DebugPrinter<'x, 't, 'p, std::rc::Rc<A>>
where
    A: Clone,
    DebugPrinter<'x, 't, 'p, A>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?}",
            &self.ctx.debug_print(self.elem_to_print.as_ref().clone())
        )
    }
}
impl<'x, 't, 'p, A> std::fmt::Debug for DebugPrinter<'x, 't, 'p, Option<A>>
where
    A: Copy,
    DebugPrinter<'x, 't, 'p, A>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.elem_to_print {
            None => write!(f, "None"),
            Some(ref x) => write!(f, "Some({:?})", self.ctx.debug_print(*x)),
        }
    }
}

impl<'t> std::fmt::Debug for DebugPrinter<'_, 't, '_, LevelPtr<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Level::{IMax, Max, Param, Succ, Zero};
        match *self.elem_to_print {
            Zero => write!(f, "0"),
            Succ(..) => {
                let (val, n) = self.ctx.level_succs(self.elem_to_print);
                if *val == Zero {
                    write!(f, "{n}")
                } else {
                    write!(f, "{:?} + {}", self.ctx.debug_print(val), n)
                }
            }
            Max(l, r, _) => {
                write!(f, "max{:?}", self.ctx.debug_print((l, r)))
            }
            IMax(l, r, _) => {
                write!(f, "imax{:?}", self.ctx.debug_print((l, r)))
            }
            Param(name, _) => {
                write!(f, "{:?}", self.ctx.debug_print(name))
            }
        }
    }
}

impl<'t> std::fmt::Debug for DebugPrinter<'_, 't, '_, ExprPtr<'t>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self.elem_to_print {
            Var { dbj_idx, .. } => write!(f, "${dbj_idx}"),
            Sort { level, .. } => write!(f, "Sort({:?})", self.ctx.debug_print(level)),
            Const { name, levels, .. } => {
                let levels = levels.as_ref();
                write!(
                    f,
                    "{:?}.{:?}",
                    self.ctx.debug_print(name),
                    self.ctx.debug_print(levels.as_ref())
                )
            }
            App { fun, arg, .. } => write!(
                f,
                "({:?} {:?})",
                self.ctx.debug_print(fun),
                self.ctx.debug_print(arg)
            ),
            Let {
                data:
                    &crate::term::expr::LetData {
                        val,
                        binder_type: binder,
                        body,
                        ..
                    },
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
            Pi {
                binder_type, body, ..
            } => {
                write!(
                    f,
                    "Pi (_ : {:?}), {:?}",
                    self.ctx.debug_print(binder_type),
                    self.ctx.debug_print(body)
                )
            }
            Lambda {
                binder_type, body, ..
            } => {
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
            NatLit { ptr, .. } => write!(f, "NLit({})", ptr.as_ref()),
            StringLit { ptr, .. } => write!(f, "SLit({})", ptr.as_ref()),
        }
    }
}

impl<'t> std::fmt::Debug for DebugPrinter<'_, 't, '_, crate::term::ptr::LevelsPtr<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?}",
            self.ctx.debug_print(self.elem_to_print.as_ref().as_ref())
        )
    }
}
impl<'t> std::fmt::Debug for DebugPrinter<'_, 't, '_, crate::term::ptr::StringPtr<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.elem_to_print.as_ref())
    }
}
impl<'t> std::fmt::Debug for DebugPrinter<'_, 't, '_, crate::term::ptr::BigUintPtr<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.elem_to_print.as_ref())
    }
}

impl<'t> std::fmt::Debug for DebugPrinter<'_, 't, '_, &crate::checker::env::DeclarInfo<'t>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeclarInfo")
            .field("name", &self.ctx.debug_print(self.elem_to_print.name))
            .field("ty", &self.ctx.debug_print(self.elem_to_print.ty))
            .field(
                "uparams",
                &self
                    .ctx
                    .debug_print(self.elem_to_print.uparams.as_ref().as_ref()),
            )
            .finish()
    }
}

impl<'t> std::fmt::Debug for DebugPrinter<'_, 't, '_, crate::checker::env::RecRule<'t>> {
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

impl std::fmt::Debug for DebugPrinter<'_, '_, '_, crate::checker::env::ReducibilityHint> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.elem_to_print)
    }
}
