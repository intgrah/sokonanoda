// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::term::expr::ExprNode;
use crate::term::id::{ANON, LevelId, NameId, StrId};
use crate::term::level::Level;
use crate::term::name::{Name, NatRed};
use hashbrown::HashTable;
use num_bigint::BigUint;
use rustc_hash::FxBuildHasher;
use std::borrow::Borrow;
use std::hash::{BuildHasher, Hash};

pub(crate) struct Interner<T> {
    pub(crate) items: Vec<T>,
    table: HashTable<u32>,
}

impl<T> Default for Interner<T> {
    fn default() -> Self {
        Self {
            items: Vec::new(),
            table: HashTable::new(),
        }
    }
}

impl<T: Hash + Eq> Interner<T> {
    pub(crate) fn with_capacity(cap: usize) -> Self {
        Self {
            items: Vec::with_capacity(cap),
            table: HashTable::with_capacity(cap),
        }
    }

    pub(crate) fn find<Q: ?Sized + Hash + Eq>(&self, q: &Q) -> Option<u32>
    where
        T: Borrow<Q>,
    {
        let items = &self.items;
        self.table
            .find(FxBuildHasher.hash_one(q), |&i| {
                items[i as usize].borrow() == q
            })
            .copied()
    }

    pub(crate) fn push(&mut self, t: T) -> u32 {
        let i = u32::try_from(self.items.len()).expect("term store exceeds u32");
        self.items.push(t);
        i
    }

    pub(crate) fn insert_unique(&mut self, t: T) -> u32 {
        let hash = FxBuildHasher.hash_one(&t);
        let i = self.push(t);
        let items = &self.items;
        self.table
            .insert_unique(hash, i, |&j| FxBuildHasher.hash_one(&items[j as usize]));
        i
    }

    pub(crate) fn intern(&mut self, t: T) -> u32 {
        match self.find(&t) {
            Some(i) => i,
            None => self.insert_unique(t),
        }
    }

    pub(crate) fn intern_ref<Q: ?Sized + Hash + Eq>(&mut self, q: &Q) -> u32
    where
        T: Borrow<Q>,
        for<'q> &'q Q: Into<T>,
    {
        match self.find(q) {
            Some(i) => i,
            None => self.insert_unique(q.into()),
        }
    }
}

#[derive(Default)]
pub struct Terms {
    pub(crate) names: Interner<Name>,
    pub(crate) levels: Interner<Level>,
    pub(crate) lists: Interner<Box<[LevelId]>>,
    pub(crate) exprs: Interner<ExprNode>,
    pub(crate) strings: Interner<Box<str>>,
    pub(crate) bignums: Interner<BigUint>,
}

impl Terms {
    pub(crate) fn with_input_len(input_len: usize) -> Self {
        Self {
            names: Interner::with_capacity(input_len / 1024 + 16),
            levels: Interner::default(),
            lists: Interner::default(),
            exprs: Interner::default(),
            strings: Interner::with_capacity(input_len / 16384 + 16),
            bignums: Interner::default(),
        }
    }

    fn find_name(&self, dot_separated_name: &str) -> Option<NameId> {
        let mut pfx = ANON;
        for s in dot_separated_name.split('.') {
            let name = if let Ok(num) = s.parse::<u64>() {
                Name::Num(pfx, num)
            } else {
                Name::Str(pfx, StrId::new(self.strings.find(s)?, false))
            };
            pfx = NameId::new(self.names.find(&name)?, false);
        }
        Some(pfx)
    }
}

macro_rules! name_cache {
    ($($field:ident = $path:literal $(=> $red:ident)?,)*) => {
        #[derive(Debug, Clone, Copy)]
        pub struct NameCache {
            $(pub(crate) $field: Option<NameId>,)*
        }

        impl Terms {
            pub(crate) fn mk_name_cache(&self, nat_red: &mut [Option<NatRed>]) -> NameCache {
                let cache = NameCache {
                    $($field: self.find_name($path),)*
                };
                $($(
                    if let Some(n) = cache.$field {
                        nat_red[n.index()] = Some(NatRed::$red);
                    }
                )?)*
                cache
            }
        }
    };
}

name_cache! {
    quot = "Quot",
    quot_mk = "Quot.mk",
    quot_lift = "Quot.lift",
    quot_ind = "Quot.ind",
    string = "String",
    string_of_list = "String.ofList",
    nat = "Nat",
    nat_zero = "Nat.zero",
    nat_succ = "Nat.succ" => Succ,
    nat_add = "Nat.add" => Add,
    nat_sub = "Nat.sub" => Sub,
    nat_mul = "Nat.mul" => Mul,
    nat_pow = "Nat.pow" => Pow,
    nat_mod = "Nat.mod" => Mod,
    nat_div = "Nat.div" => Div,
    nat_div_go = "Nat.div.go" => DivGo,
    nat_mod_core_go = "Nat.modCore.go" => ModCoreGo,
    nat_beq = "Nat.beq" => Beq,
    nat_ble = "Nat.ble" => Ble,
    nat_gcd = "Nat.gcd" => Gcd,
    nat_xor = "Nat.xor" => XOr,
    nat_land = "Nat.land" => LAnd,
    nat_lor = "Nat.lor" => LOr,
    nat_shl = "Nat.shiftLeft" => Shl,
    nat_shr = "Nat.shiftRight" => Shr,
    bool_true = "Bool.true",
    bool_false = "Bool.false",
    char = "Char",
    char_of_nat = "Char.ofNat",
    list_nil = "List.nil",
    list_cons = "List.cons",
}
