//! Implementaiton of the `Name` type (hierarchical names)
use crate::util::{CowStr, NamePtr, StringPtr, TcCtx};
use Name::*;

pub(crate) const ANON_HASH: u64 = 43;
pub(crate) const STR_HASH: u64 = 911;
pub(crate) const NUM_HASH: u64 = 103;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Name<'a> {
    Anon,
    Str(NamePtr<'a>, StringPtr<'a>, u64),
    Num(NamePtr<'a>, u64, u64),
}

impl<'a> std::hash::Hash for Name<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

impl<'a> Name<'a> {
    pub(crate) fn get_hash(&self) -> u64 {
        match self {
            Anon => ANON_HASH,
            Str(.., hash) | Num(.., hash) => *hash,
        }
    }
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
        use NatRed::*;
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

pub struct NameNode<'a> {
    pub(crate) kind: Name<'a>,
    decl_idx: std::sync::atomic::AtomicU32,
    nat_red: std::sync::atomic::AtomicU8,
}

impl<'a> NameNode<'a> {
    pub(crate) fn new(kind: Name<'a>) -> Self {
        Self {
            kind,
            decl_idx: std::sync::atomic::AtomicU32::new(NO_DECL),
            nat_red: std::sync::atomic::AtomicU8::new(NO_NAT_RED),
        }
    }

    #[inline]
    pub(crate) fn decl_idx(&self) -> u32 { self.decl_idx.load(std::sync::atomic::Ordering::Relaxed) }

    #[inline]
    pub(crate) fn set_decl_idx(&self, idx: u32) { self.decl_idx.store(idx, std::sync::atomic::Ordering::Relaxed) }

    #[inline]
    pub(crate) fn is_nat_red(&self) -> bool {
        self.nat_red.load(std::sync::atomic::Ordering::Relaxed) != NO_NAT_RED
    }

    #[inline]
    pub(crate) fn nat_red(&self) -> Option<NatRed> {
        NatRed::from_u8(self.nat_red.load(std::sync::atomic::Ordering::Relaxed))
    }

    #[inline]
    pub(crate) fn set_nat_red(&self, k: NatRed) {
        self.nat_red.store(k as u8, std::sync::atomic::Ordering::Relaxed)
    }
}

impl<'a> PartialEq for NameNode<'a> {
    #[inline]
    fn eq(&self, o: &Self) -> bool { self.kind == o.kind }
}
impl<'a> Eq for NameNode<'a> {}

impl<'a> crate::util::RawHash for NameNode<'a> {
    #[inline]
    fn raw_hash(&self) -> u64 { self.kind.get_hash() }
}

impl<'a> std::fmt::Debug for NameNode<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.kind.fmt(f) }
}

impl<'x, 't: 'x, 'p: 't> TcCtx<'t, 'p> {
    pub(crate) fn concat_name(&mut self, n1: NamePtr<'t>, n2: NamePtr<'t>) -> NamePtr<'t> {
        match self.read_name(n2) {
            Anon => n1,
            Str(pfx, sfx, ..) => {
                let pfx = self.concat_name(n1, pfx);
                self.str(pfx, sfx)
            }
            Num(pfx, sfx, ..) => {
                let pfx = self.concat_name(n1, pfx);
                self.num(pfx, sfx)
            }
        }
    }

    pub(crate) fn append_index_after(&mut self, n: NamePtr<'t>, idx: u64) -> NamePtr<'t> {
        match self.read_name(n) {
            Str(pfx, sfx, ..) => {
                let s = self.read_string(sfx);
                let s = self.alloc_string(CowStr::Owned(format!("{}_{}", s, idx)));
                self.str(pfx, s)
            }
            _ => {
                let s = self.alloc_string(CowStr::Owned(format!("_{}", idx)));
                self.str(n, s)
            }
        }
    }

    pub(crate) fn replace_pfx(&mut self, n: NamePtr<'t>, outgoing: NamePtr<'t>, incoming: NamePtr<'t>) -> NamePtr<'t> {
        match self.read_name(n) {
            Anon => match self.read_name(outgoing) {
                Anon => incoming,
                _ => self.anonymous(),
            },
            Str(..) | Num(..) if n == outgoing => incoming,
            Str(pfx, sfx, ..) => {
                let pfx = self.replace_pfx(pfx, outgoing, incoming);
                self.str(pfx, sfx)
            }
            Num(pfx, sfx, ..) => {
                let pfx = self.replace_pfx(pfx, outgoing, incoming);
                self.num(pfx, sfx)
            }
        }
    }
}
