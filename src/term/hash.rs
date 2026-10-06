// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexMap;
use rustc_hash::{FxBuildHasher, FxHasher};
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

pub(crate) type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
pub(crate) type FxHashMap<K, V> = HashMap<K, V, FxBuildHasher>;
pub(crate) type FxHashSet<K> = HashSet<K, FxBuildHasher>;

pub(crate) type CowStr<'a> = Cow<'a, str>;

/// <https://en.wikipedia.org/wiki/Hash_function#Fibonacci_hashing>
/// 2 ^ 64 / φ
pub(crate) const GOLDEN: u64 = 0x9E37_79B9_7F4A_7C15;

pub(crate) trait StructHash {
    fn struct_hash(&self) -> u64;
}
impl<T: Hash + ?Sized> StructHash for T {
    #[inline]
    fn struct_hash(&self) -> u64 {
        let mut hasher = FxHasher::default();
        self.hash(&mut hasher);
        hasher.finish()
    }
}

pub(crate) trait RawHash {
    fn raw_hash(&self) -> u64;
}

impl RawHash for CowStr<'_> {
    #[inline]
    fn raw_hash(&self) -> u64 {
        self.struct_hash()
    }
}

pub(crate) fn new_fx_index_map<K, V>() -> FxIndexMap<K, V> {
    FxIndexMap::with_hasher(FxBuildHasher)
}

pub(crate) fn new_fx_hash_map<K, V>() -> FxHashMap<K, V> {
    FxHashMap::with_hasher(FxBuildHasher)
}

pub(crate) fn new_fx_hash_set<K>() -> FxHashSet<K> {
    FxHashSet::with_hasher(FxBuildHasher)
}

#[macro_export]
macro_rules! hash64 {
    ( $( $x:expr ),* ) => {
        {
            use std::hash::{ Hash, Hasher };
            let mut hasher = rustc_hash::FxHasher::default();
            $(
                ($x).hash(&mut hasher);
            )*
            hasher.finish()
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::Config;
    use crate::frontend::parser::parse_export_file;
    use num_bigint::BigRng010;
    use rand::RngExt;
    use rand::distr::Alphanumeric;
    use std::error::Error;

    #[test]
    fn hash_eq_of_eq() -> Result<(), Box<dyn Error>> {
        let arena = bumpalo::Bump::new();
        let export = parse_export_file(&arena, std::io::empty(), Config::default())?;
        let mut rng = rand::rng();
        export.with_ctx(|ctx, _cache, _arena| {
            for size in 0..100 {
                for _ in 0..100 {
                    let text: String = (&mut rng)
                        .sample_iter(Alphanumeric)
                        .take(size)
                        .map(char::from)
                        .collect();
                    let text = CowStr::Owned(text);
                    let (left, right) = (
                        ctx.mk_string_lit_quick(text.clone()),
                        ctx.mk_string_lit_quick(text),
                    );
                    assert_eq!(hash64!(left), hash64!(right));
                    assert_eq!(left, right);

                    let nat = rng.random_biguint(size as u64);
                    let (left, right) =
                        (ctx.mk_nat_lit_quick(nat.clone()), ctx.mk_nat_lit_quick(nat));
                    assert_eq!(hash64!(left), hash64!(right));
                    assert_eq!(left, right);
                }
            }
        });
        Ok(())
    }
}
