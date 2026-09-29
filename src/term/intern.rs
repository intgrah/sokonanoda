use super::hash::{CowStr, RawHash, StructHash};
use super::ptr::{LevelPtr, NamePtr, StringPtr};
use crate::config::Config;
use crate::hash64;
use crate::term::expr::Expr;
use crate::term::level::Level;
use crate::term::name::{Name, NUM_HASH, STR_HASH};
use bumpalo::Bump;
use hashbrown::HashTable;
use num_bigint::BigUint;

macro_rules! interner {
    ($name:ident, $pointee:ident) => {
        pub(crate) struct $name<'a> {
            table: HashTable<&'a $pointee<'a>>,
        }
        impl<'a> $name<'a> {
            fn new() -> Self {
                Self {
                    table: HashTable::new(),
                }
            }
            #[allow(dead_code)]
            fn with_capacity(cap: usize) -> Self {
                Self {
                    table: HashTable::with_capacity(cap),
                }
            }
            #[allow(dead_code)]
            pub(crate) fn len(&self) -> usize {
                self.table.len()
            }

            #[allow(dead_code)]
            pub(crate) fn clear(&mut self) {
                self.table.clear()
            }

            pub(crate) fn get<'b>(&self, v: &$pointee<'b>) -> Option<&'a $pointee<'a>>
            where
                'a: 'b,
            {
                let hash = v.raw_hash();
                self.table
                    .find(hash, |stored| {
                        let s: &$pointee<'b> = stored;
                        s == v
                    })
                    .copied()
            }

            pub(crate) fn insert(&mut self, arena: &'a Bump, v: $pointee<'a>) -> &'a $pointee<'a> {
                let hash = v.raw_hash();
                let r: &'a $pointee<'a> = arena.alloc(v);
                self.table.insert_unique(hash, r, |s| s.raw_hash());
                r
            }

            #[allow(dead_code)]
            pub(crate) fn intern(&mut self, arena: &'a Bump, v: $pointee<'a>) -> &'a $pointee<'a> {
                if let Some(r) = self.get(&v) {
                    return r;
                }
                self.insert(arena, v)
            }
        }
    };
}

pub(crate) struct NameInterner<'a> {
    table: HashTable<&'a crate::term::name::NameNode<'a>>,
}
impl<'a> NameInterner<'a> {
    fn new() -> Self {
        Self {
            table: HashTable::new(),
        }
    }

    fn with_capacity(cap: usize) -> Self {
        Self {
            table: HashTable::with_capacity(cap),
        }
    }

    pub(crate) fn get<'b>(&self, v: &Name<'b>) -> Option<&'a crate::term::name::NameNode<'a>>
    where
        'a: 'b,
    {
        let hash = v.get_hash();
        self.table
            .find(hash, |stored| match (&stored.kind, v) {
                (Name::Anon, Name::Anon) => true,
                (Name::Str(a, x, h), Name::Str(b, y, k)) => {
                    h == k && a.get_hash() == b.get_hash() && x.get_hash() == y.get_hash()
                }
                (Name::Num(a, x, h), Name::Num(b, y, k)) => {
                    h == k && a.get_hash() == b.get_hash() && x == y
                }
                _ => false,
            })
            .copied()
    }

    pub(crate) fn insert(
        &mut self,
        arena: &'a Bump,
        v: Name<'a>,
    ) -> &'a crate::term::name::NameNode<'a> {
        let hash = v.get_hash();
        let r: &'a crate::term::name::NameNode<'a> =
            arena.alloc(crate::term::name::NameNode::new(v));
        self.table.insert_unique(hash, r, |s| s.kind.get_hash());
        r
    }

    pub(crate) fn intern(
        &mut self,
        arena: &'a Bump,
        v: Name<'a>,
    ) -> &'a crate::term::name::NameNode<'a> {
        if let Some(r) = self.get(&v) {
            return r;
        }
        self.insert(arena, v)
    }
}

interner!(LevelInterner, Level);
interner!(ExprInterner, Expr);
interner!(StringInterner, CowStr);

impl<'a> ExprInterner<'a> {}

pub(crate) struct BigUintInterner<'a> {
    table: HashTable<&'a BigUint>,
}
impl<'a> BigUintInterner<'a> {
    fn new() -> Self {
        Self {
            table: HashTable::new(),
        }
    }
    pub(crate) fn get(&self, v: &BigUint) -> Option<&'a BigUint> {
        let hash = v.struct_hash();
        self.table.find(hash, |stored| **stored == *v).copied()
    }
    pub(crate) fn insert(&mut self, arena: &'a Bump, v: BigUint) -> &'a BigUint {
        let hash = v.struct_hash();
        let r: &'a BigUint = arena.alloc(v);
        self.table.insert_unique(hash, r, |s| s.struct_hash());
        r
    }
    pub(crate) fn intern(&mut self, arena: &'a Bump, v: BigUint) -> &'a BigUint {
        if let Some(r) = self.get(&v) {
            return r;
        }
        self.insert(arena, v)
    }
}

pub(crate) struct LevelsInterner<'a> {
    table: HashTable<&'a [LevelPtr<'a>]>,
}
impl<'a> LevelsInterner<'a> {
    fn new() -> Self {
        Self {
            table: HashTable::new(),
        }
    }
    fn with_capacity(cap: usize) -> Self {
        Self {
            table: HashTable::with_capacity(cap),
        }
    }
    pub(crate) fn get<'b>(&self, v: &[LevelPtr<'b>]) -> Option<&'a [LevelPtr<'a>]>
    where
        'a: 'b,
    {
        let hash = v.struct_hash();
        self.table
            .find(hash, |stored| {
                let s: &[LevelPtr<'b>] = stored;
                s == v
            })
            .copied()
    }
    pub(crate) fn intern(&mut self, arena: &'a Bump, v: &[LevelPtr<'a>]) -> &'a [LevelPtr<'a>] {
        if let Some(r) = self.get(v) {
            return r;
        }
        let hash = v.struct_hash();
        let r: &'a [LevelPtr<'a>] = arena.alloc_slice_copy(v);
        self.table.insert_unique(hash, r, |s| s.struct_hash());
        r
    }
}

pub struct Dag<'a> {
    pub(crate) names: NameInterner<'a>,
    pub(crate) levels: LevelInterner<'a>,
    pub(crate) exprs: ExprInterner<'a>,
    pub(crate) uparams: LevelsInterner<'a>,
    pub(crate) strings: StringInterner<'a>,
    pub(crate) bignums: Option<BigUintInterner<'a>>,
}

impl<'a> Dag<'a> {
    pub(crate) fn new(config: &Config, input_len: usize) -> Self {
        Self {
            names: NameInterner::with_capacity(input_len / 1024 + 16),
            levels: LevelInterner::new(),
            exprs: ExprInterner::new(),
            uparams: LevelsInterner::new(),
            strings: StringInterner::with_capacity(input_len / 16384 + 16),
            bignums: if config.nat_extension {
                Some(BigUintInterner::new())
            } else {
                None
            },
        }
    }

    pub(crate) fn new_local(config: &Config) -> Self {
        Self {
            names: NameInterner::new(),
            levels: LevelInterner::with_capacity(14),
            exprs: ExprInterner::with_capacity(14),
            uparams: LevelsInterner::with_capacity(14),
            strings: StringInterner::new(),
            bignums: if config.nat_extension {
                Some(BigUintInterner::new())
            } else {
                None
            },
        }
    }
}

impl<'a> StringInterner<'a> {
    pub(crate) fn get_str(&self, s: &str) -> Option<&'a CowStr<'a>> {
        let hash = s.struct_hash();
        self.table
            .find(hash, |stored| stored.as_ref() == s)
            .copied()
    }
}

impl<'a> Dag<'a> {
    fn get_string_ptr(&self, s: &str) -> Option<StringPtr<'a>> {
        self.strings.get_str(s).map(StringPtr::global)
    }

    fn find_name(&self, anon: NamePtr<'a>, dot_separated_name: &str) -> Option<NamePtr<'a>> {
        let mut pfx = anon;
        for s in dot_separated_name.split('.') {
            if let Ok(num) = s.parse::<u64>() {
                let hash = hash64!(NUM_HASH, pfx, num);
                if let Some(r) = self.names.get(&Name::Num(pfx, num, hash)) {
                    pfx = NamePtr::global(r);
                    continue;
                }
            } else if let Some(sfx) = self.get_string_ptr(s) {
                let hash = hash64!(STR_HASH, pfx, sfx);
                if let Some(r) = self.names.get(&Name::Str(pfx, sfx, hash)) {
                    pfx = NamePtr::global(r);
                    continue;
                }
            }
            return None;
        }
        Some(pfx)
    }

    pub(crate) fn mk_name_cache(&self, anon: NamePtr<'a>) -> NameCache<'a> {
        let cache = self.mk_name_cache_aux(anon);
        use crate::term::name::NatRed;
        let kinds = [
            (cache.nat_succ, NatRed::Succ),
            (cache.nat_div_go, NatRed::DivGo),
            (cache.nat_mod_core_go, NatRed::ModCoreGo),
            (cache.nat_add, NatRed::Add),
            (cache.nat_sub, NatRed::Sub),
            (cache.nat_mul, NatRed::Mul),
            (cache.nat_pow, NatRed::Pow),
            (cache.nat_mod, NatRed::Mod),
            (cache.nat_div, NatRed::Div),
            (cache.nat_beq, NatRed::Beq),
            (cache.nat_ble, NatRed::Ble),
            (cache.nat_land, NatRed::LAnd),
            (cache.nat_lor, NatRed::LOr),
            (cache.nat_xor, NatRed::XOr),
            (cache.nat_gcd, NatRed::Gcd),
            (cache.nat_shl, NatRed::Shl),
            (cache.nat_shr, NatRed::Shr),
        ];
        for (n, k) in kinds {
            if let Some(n) = n {
                n.as_ref().set_nat_red(k);
            }
        }
        cache
    }

    fn mk_name_cache_aux(&self, anon: NamePtr<'a>) -> NameCache<'a> {
        NameCache {
            quot: self.find_name(anon, "Quot"),
            quot_mk: self.find_name(anon, "Quot.mk"),
            quot_lift: self.find_name(anon, "Quot.lift"),
            quot_ind: self.find_name(anon, "Quot.ind"),
            string: self.find_name(anon, "String"),
            string_of_list: self.find_name(anon, "String.ofList"),
            nat: self.find_name(anon, "Nat"),
            nat_zero: self.find_name(anon, "Nat.zero"),
            nat_succ: self.find_name(anon, "Nat.succ"),
            nat_add: self.find_name(anon, "Nat.add"),
            nat_sub: self.find_name(anon, "Nat.sub"),
            nat_mul: self.find_name(anon, "Nat.mul"),
            nat_pow: self.find_name(anon, "Nat.pow"),
            nat_mod: self.find_name(anon, "Nat.mod"),
            nat_div: self.find_name(anon, "Nat.div"),
            nat_div_go: self.find_name(anon, "Nat.div.go"),
            nat_mod_core_go: self.find_name(anon, "Nat.modCore.go"),
            nat_beq: self.find_name(anon, "Nat.beq"),
            nat_ble: self.find_name(anon, "Nat.ble"),
            nat_gcd: self.find_name(anon, "Nat.gcd"),
            nat_xor: self.find_name(anon, "Nat.xor"),
            nat_land: self.find_name(anon, "Nat.land"),
            nat_lor: self.find_name(anon, "Nat.lor"),
            nat_shl: self.find_name(anon, "Nat.shiftLeft"),
            nat_shr: self.find_name(anon, "Nat.shiftRight"),
            bool_true: self.find_name(anon, "Bool.true"),
            bool_false: self.find_name(anon, "Bool.false"),
            char: self.find_name(anon, "Char"),
            char_of_nat: self.find_name(anon, "Char.ofNat"),
            list: self.find_name(anon, "List"),
            list_nil: self.find_name(anon, "List.nil"),
            list_cons: self.find_name(anon, "List.cons"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct NameCache<'p> {
    pub(crate) quot: Option<NamePtr<'p>>,
    pub(crate) quot_mk: Option<NamePtr<'p>>,
    pub(crate) quot_lift: Option<NamePtr<'p>>,
    pub(crate) quot_ind: Option<NamePtr<'p>>,
    pub(crate) nat: Option<NamePtr<'p>>,
    pub(crate) nat_zero: Option<NamePtr<'p>>,
    pub(crate) nat_succ: Option<NamePtr<'p>>,
    pub(crate) nat_add: Option<NamePtr<'p>>,
    pub(crate) nat_sub: Option<NamePtr<'p>>,
    pub(crate) nat_mul: Option<NamePtr<'p>>,
    pub(crate) nat_pow: Option<NamePtr<'p>>,
    pub(crate) nat_mod: Option<NamePtr<'p>>,
    pub(crate) nat_div: Option<NamePtr<'p>>,
    pub(crate) nat_div_go: Option<NamePtr<'p>>,
    pub(crate) nat_mod_core_go: Option<NamePtr<'p>>,
    pub(crate) nat_beq: Option<NamePtr<'p>>,
    pub(crate) nat_ble: Option<NamePtr<'p>>,
    pub(crate) nat_gcd: Option<NamePtr<'p>>,
    pub(crate) nat_xor: Option<NamePtr<'p>>,
    pub(crate) nat_land: Option<NamePtr<'p>>,
    pub(crate) nat_lor: Option<NamePtr<'p>>,
    pub(crate) nat_shr: Option<NamePtr<'p>>,
    pub(crate) nat_shl: Option<NamePtr<'p>>,
    pub(crate) string: Option<NamePtr<'p>>,
    pub(crate) string_of_list: Option<NamePtr<'p>>,
    pub(crate) bool_false: Option<NamePtr<'p>>,
    pub(crate) bool_true: Option<NamePtr<'p>>,
    pub(crate) char: Option<NamePtr<'p>>,
    pub(crate) char_of_nat: Option<NamePtr<'p>>,
    #[allow(dead_code)]
    pub(crate) list: Option<NamePtr<'p>>,
    pub(crate) list_nil: Option<NamePtr<'p>>,
    pub(crate) list_cons: Option<NamePtr<'p>>,
}
