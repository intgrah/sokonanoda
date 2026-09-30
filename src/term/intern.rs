use super::hash::{CowStr, RawHash, StructHash};
use super::ptr::{LevelPtr, NamePtr, StringPtr};
use crate::config::Config;
use crate::hash64;
use crate::term::expr::Expr;
use crate::term::level::Level;
use crate::term::name::{NUM_HASH, Name, NameNode, NatRed, STR_HASH};
use bumpalo::Bump;
use hashbrown::HashTable;
use num_bigint::BigUint;

pub(crate) trait Internable<'a>: 'a {
    type Query<'b>: ?Sized
    where
        'a: 'b;
    type Owned<'x>
    where
        'a: 'x;
    fn query_hash<'b>(q: &Self::Query<'b>) -> u64
    where
        'a: 'b;
    fn stored_hash(&self) -> u64;
    fn matches<'b>(&self, q: &Self::Query<'b>) -> bool
    where
        'a: 'b;
    fn as_query<'s, 'x>(v: &'s Self::Owned<'x>) -> &'s Self::Query<'a>
    where
        'a: 'x;
    fn alloc<'x>(arena: &'a Bump, v: Self::Owned<'x>) -> &'a Self
    where
        'a: 'x;
}

pub(crate) struct Interner<'a, T: ?Sized> {
    table: HashTable<&'a T>,
}

impl<'a, T: ?Sized + Internable<'a>> Interner<'a, T> {
    fn with_capacity(cap: usize) -> Self {
        Self {
            table: HashTable::with_capacity(cap),
        }
    }

    pub(crate) fn get<'b>(&self, q: &T::Query<'b>) -> Option<&'a T>
    where
        'a: 'b,
    {
        self.table
            .find(T::query_hash(q), |stored| stored.matches(q))
            .copied()
    }

    pub(crate) fn insert<'x>(&mut self, arena: &'a Bump, v: T::Owned<'x>) -> &'a T
    where
        'a: 'x,
    {
        let r = T::alloc(arena, v);
        self.table
            .insert_unique(r.stored_hash(), r, |s| s.stored_hash());
        r
    }

    pub(crate) fn intern<'x>(&mut self, arena: &'a Bump, v: T::Owned<'x>) -> &'a T
    where
        'a: 'x,
    {
        if let Some(r) = self.get(T::as_query(&v)) {
            return r;
        }
        self.insert(arena, v)
    }
}

macro_rules! internable_by_value {
    ($t:ident) => {
        impl<'a> Internable<'a> for $t<'a> {
            type Query<'b>
                = $t<'b>
            where
                'a: 'b;
            type Owned<'x>
                = $t<'a>
            where
                'a: 'x;
            fn query_hash<'b>(q: &$t<'b>) -> u64
            where
                'a: 'b,
            {
                q.raw_hash()
            }
            fn stored_hash(&self) -> u64 {
                self.raw_hash()
            }
            fn matches<'b>(&self, q: &$t<'b>) -> bool
            where
                'a: 'b,
            {
                let s: &$t<'b> = self;
                s == q
            }
            fn as_query<'s, 'x>(v: &'s $t<'a>) -> &'s $t<'a>
            where
                'a: 'x,
            {
                v
            }
            fn alloc<'x>(arena: &'a Bump, v: $t<'a>) -> &'a Self
            where
                'a: 'x,
            {
                arena.alloc(v)
            }
        }
    };
}

internable_by_value!(Level);
internable_by_value!(Expr);

impl<'a> Internable<'a> for CowStr<'a> {
    type Query<'b>
        = str
    where
        'a: 'b;
    type Owned<'x>
        = CowStr<'a>
    where
        'a: 'x;
    fn query_hash<'b>(q: &str) -> u64
    where
        'a: 'b,
    {
        q.struct_hash()
    }
    fn stored_hash(&self) -> u64 {
        self.raw_hash()
    }
    fn matches<'b>(&self, q: &str) -> bool
    where
        'a: 'b,
    {
        self.as_ref() == q
    }
    fn as_query<'s, 'x>(v: &'s CowStr<'a>) -> &'s str
    where
        'a: 'x,
    {
        v.as_ref()
    }
    fn alloc<'x>(arena: &'a Bump, v: CowStr<'a>) -> &'a Self
    where
        'a: 'x,
    {
        arena.alloc(v)
    }
}

impl<'a> Internable<'a> for NameNode<'a> {
    type Query<'b>
        = Name<'b>
    where
        'a: 'b;
    type Owned<'x>
        = Name<'a>
    where
        'a: 'x;
    fn query_hash<'b>(q: &Name<'b>) -> u64
    where
        'a: 'b,
    {
        q.get_hash()
    }
    fn stored_hash(&self) -> u64 {
        self.kind.get_hash()
    }
    fn matches<'b>(&self, q: &Name<'b>) -> bool
    where
        'a: 'b,
    {
        match (&self.kind, q) {
            (Name::Anon, Name::Anon) => true,
            (Name::Str(a, x, h), Name::Str(b, y, k)) => {
                h == k && a.get_hash() == b.get_hash() && x.get_hash() == y.get_hash()
            }
            (Name::Num(a, x, h), Name::Num(b, y, k)) => {
                h == k && a.get_hash() == b.get_hash() && x == y
            }
            _ => false,
        }
    }
    fn as_query<'s, 'x>(v: &'s Name<'a>) -> &'s Name<'a>
    where
        'a: 'x,
    {
        v
    }
    fn alloc<'x>(arena: &'a Bump, v: Name<'a>) -> &'a Self
    where
        'a: 'x,
    {
        arena.alloc(NameNode::new(v))
    }
}

impl<'a> Internable<'a> for BigUint {
    type Query<'b>
        = BigUint
    where
        'a: 'b;
    type Owned<'x>
        = BigUint
    where
        'a: 'x;
    fn query_hash<'b>(q: &BigUint) -> u64
    where
        'a: 'b,
    {
        q.struct_hash()
    }
    fn stored_hash(&self) -> u64 {
        self.struct_hash()
    }
    fn matches<'b>(&self, q: &BigUint) -> bool
    where
        'a: 'b,
    {
        self == q
    }
    fn as_query<'s, 'x>(v: &'s BigUint) -> &'s BigUint
    where
        'a: 'x,
    {
        v
    }
    fn alloc<'x>(arena: &'a Bump, v: BigUint) -> &'a Self
    where
        'a: 'x,
    {
        arena.alloc(v)
    }
}

impl<'a> Internable<'a> for [LevelPtr<'a>] {
    type Query<'b>
        = [LevelPtr<'b>]
    where
        'a: 'b;
    type Owned<'x>
        = &'x [LevelPtr<'a>]
    where
        'a: 'x;
    fn query_hash<'b>(q: &[LevelPtr<'b>]) -> u64
    where
        'a: 'b,
    {
        q.struct_hash()
    }
    fn stored_hash(&self) -> u64 {
        self.struct_hash()
    }
    fn matches<'b>(&self, q: &[LevelPtr<'b>]) -> bool
    where
        'a: 'b,
    {
        let s: &[LevelPtr<'b>] = self;
        s == q
    }
    fn as_query<'s, 'x>(v: &'s &'x [LevelPtr<'a>]) -> &'s [LevelPtr<'a>]
    where
        'a: 'x,
    {
        v
    }
    fn alloc<'x>(arena: &'a Bump, v: &'x [LevelPtr<'a>]) -> &'a Self
    where
        'a: 'x,
    {
        arena.alloc_slice_copy(v)
    }
}

pub struct Dag<'a> {
    pub(crate) names: Interner<'a, NameNode<'a>>,
    pub(crate) levels: Interner<'a, Level<'a>>,
    pub(crate) exprs: Interner<'a, Expr<'a>>,
    pub(crate) uparams: Interner<'a, [LevelPtr<'a>]>,
    pub(crate) strings: Interner<'a, CowStr<'a>>,
    pub(crate) bignums: Option<Interner<'a, BigUint>>,
}

impl<'a> Dag<'a> {
    pub(crate) fn new(config: &Config, input_len: usize) -> Self {
        Self {
            names: Interner::with_capacity(input_len / 1024 + 16),
            levels: Interner::with_capacity(0),
            exprs: Interner::with_capacity(0),
            uparams: Interner::with_capacity(0),
            strings: Interner::with_capacity(input_len / 16384 + 16),
            bignums: config.nat_extension.then(|| Interner::with_capacity(0)),
        }
    }

    pub(crate) fn new_local(config: &Config) -> Self {
        Self {
            names: Interner::with_capacity(0),
            levels: Interner::with_capacity(14),
            exprs: Interner::with_capacity(14),
            uparams: Interner::with_capacity(14),
            strings: Interner::with_capacity(0),
            bignums: config.nat_extension.then(|| Interner::with_capacity(0)),
        }
    }
}

impl<'a> Dag<'a> {
    fn get_string_ptr(&self, s: &str) -> Option<StringPtr<'a>> {
        self.strings.get(s).map(StringPtr::global)
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
}

macro_rules! name_cache {
    ($($field:ident = $path:literal $(=> $red:ident)?,)*) => {
        #[derive(Debug, Clone, Copy)]
        pub struct NameCache<'p> {
            $(pub(crate) $field: Option<NamePtr<'p>>,)*
        }

        impl<'a> Dag<'a> {
            pub(crate) fn mk_name_cache(&self, anon: NamePtr<'a>) -> NameCache<'a> {
                let cache = NameCache {
                    $($field: self.find_name(anon, $path),)*
                };
                $($(
                    if let Some(n) = cache.$field {
                        n.as_ref().set_nat_red(NatRed::$red);
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
