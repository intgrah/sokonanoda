// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

//! Implementaiton of the `Name` type (hierarchical names)
use crate::checker::context::TcCtx;
use crate::term::id::{ANON, NameId, StrId};
use Name::{Anon, Num, Str};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Name {
    Anon,
    Str(NameId, StrId),
    Num(NameId, u64),
}

pub(crate) const NO_DECL: u32 = u32::MAX;

pub(crate) const NO_NAT_RED: u8 = u8::MAX;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum NatRed {
    Succ,
    DivGo,
    ModCoreGo,
    Add,
    Sub,
    Mul,
    Pow,
    Mod,
    Div,
    Beq,
    Ble,
    LAnd,
    LOr,
    XOr,
    Gcd,
    Shl,
    Shr,
}

impl NatRed {
    pub(crate) fn from_u8(k: u8) -> Option<Self> {
        use NatRed::{
            Add, Beq, Ble, Div, DivGo, Gcd, LAnd, LOr, Mod, ModCoreGo, Mul, Pow, Shl, Shr, Sub,
            Succ, XOr,
        };
        Some(match k {
            0 => Succ,
            1 => DivGo,
            2 => ModCoreGo,
            3 => Add,
            4 => Sub,
            5 => Mul,
            6 => Pow,
            7 => Mod,
            8 => Div,
            9 => Beq,
            10 => Ble,
            11 => LAnd,
            12 => LOr,
            13 => XOr,
            14 => Gcd,
            15 => Shl,
            16 => Shr,
            _ => return None,
        })
    }
}

pub(crate) trait NameSource {
    fn name(&self, n: NameId) -> Name;
    fn string(&self, s: StrId) -> &str;
}

pub(crate) struct NameDisplay<'a, S: NameSource> {
    pub(crate) src: &'a S,
    pub(crate) name: NameId,
}

impl<S: NameSource> fmt::Display for NameDisplay<'_, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.src.name(self.name) {
            Anon => Ok(()),
            Str(pfx, sfx) => {
                self.write_prefix(f, pfx)?;
                f.write_str(self.src.string(sfx))
            }
            Num(pfx, sfx) => {
                self.write_prefix(f, pfx)?;
                write!(f, "{sfx}")
            }
        }
    }
}

impl<S: NameSource> NameDisplay<'_, S> {
    fn write_prefix(&self, f: &mut fmt::Formatter<'_>, pfx: NameId) -> fmt::Result {
        if pfx == ANON {
            return Ok(());
        }
        let prefix = NameDisplay {
            src: self.src,
            name: pfx,
        };
        write!(f, "{prefix}.")
    }
}

impl<'t> TcCtx<'t> {
    pub(crate) fn concat_name(&mut self, n1: NameId, n2: NameId) -> NameId {
        match self.name(n2) {
            Anon => n1,
            Str(pfx, sfx) => {
                let pfx = self.concat_name(n1, pfx);
                self.str(pfx, sfx)
            }
            Num(pfx, sfx) => {
                let pfx = self.concat_name(n1, pfx);
                self.num(pfx, sfx)
            }
        }
    }

    pub(crate) fn append_index_after(&mut self, n: NameId, idx: u64) -> NameId {
        if let Str(pfx, sfx) = self.name(n) {
            let s = format!("{}_{idx}", self.string(sfx));
            let s = self.alloc_string(&s);
            self.str(pfx, s)
        } else {
            let s = self.alloc_string(&format!("_{idx}"));
            self.str(n, s)
        }
    }

    pub(crate) fn replace_pfx(&mut self, n: NameId, outgoing: NameId, incoming: NameId) -> NameId {
        match self.name(n) {
            Anon => match self.name(outgoing) {
                Anon => incoming,
                _ => ANON,
            },
            Str(..) | Num(..) if n == outgoing => incoming,
            Str(pfx, sfx) => {
                let pfx = self.replace_pfx(pfx, outgoing, incoming);
                self.str(pfx, sfx)
            }
            Num(pfx, sfx) => {
                let pfx = self.replace_pfx(pfx, outgoing, incoming);
                self.num(pfx, sfx)
            }
        }
    }
}
