// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::Reset;
use crate::checker::value::{E, LsubId, V};
use crate::term::hash::GOLDEN;
use crate::term::id::{ExprId, LevelId, LevelsId, NameId};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicU32, Ordering};

pub(crate) trait Word: Copy {
    fn word(self) -> u64;
}

pub(crate) trait Half: Copy {
    fn half(self) -> u32;
}

macro_rules! id_keys {
    ($($t:ty),*) => {
        $(
            impl Word for $t {
                #[inline(always)]
                fn word(self) -> u64 {
                    u64::from(self.raw())
                }
            }

            impl Half for $t {
                #[inline(always)]
                fn half(self) -> u32 {
                    self.raw()
                }
            }
        )*
    };
}

id_keys!(ExprId, NameId, LevelId, LevelsId, V, E, LsubId);

impl Half for u16 {
    #[inline(always)]
    fn half(self) -> u32 {
        u32::from(self)
    }
}

impl Half for u32 {
    #[inline(always)]
    fn half(self) -> u32 {
        self
    }
}

impl Word for u64 {
    #[inline(always)]
    fn word(self) -> u64 {
        self
    }
}

#[inline(always)]
fn pack<A: Half, B: Half>(a: A, b: B) -> u64 {
    (u64::from(a.half()) << 32) | u64::from(b.half())
}

pub(crate) trait Key: Copy {
    type Words: Copy + Eq;
    fn words(self) -> Self::Words;
    fn hash(w: &Self::Words) -> u64;
}

const SECOND: u64 = 0xC2B2_AE3D_27D4_EB4F;

impl<A: Word> Key for A {
    type Words = [u64; 1];
    #[inline(always)]
    fn words(self) -> [u64; 1] {
        [self.word()]
    }
    #[inline(always)]
    fn hash(w: &[u64; 1]) -> u64 {
        w[0].wrapping_mul(GOLDEN)
    }
}

impl<A: Half, B: Half> Key for (A, B) {
    type Words = [u64; 1];
    #[inline(always)]
    fn words(self) -> [u64; 1] {
        [pack(self.0, self.1)]
    }
    #[inline(always)]
    fn hash(w: &[u64; 1]) -> u64 {
        w[0].wrapping_mul(GOLDEN)
    }
}

impl<A: Half, B: Half, C: Half> Key for (A, B, C) {
    type Words = [u64; 2];
    #[inline(always)]
    fn words(self) -> [u64; 2] {
        [pack(self.0, self.1), u64::from(self.2.half())]
    }
    #[inline(always)]
    fn hash(w: &[u64; 2]) -> u64 {
        w[0].wrapping_mul(GOLDEN) ^ w[1].wrapping_mul(SECOND)
    }
}

impl Key for (u64, u64, u64) {
    type Words = [u64; 3];
    #[inline(always)]
    fn words(self) -> [u64; 3] {
        [self.0, self.1, self.2]
    }
    #[inline(always)]
    fn hash(w: &[u64; 3]) -> u64 {
        let h = w[0].wrapping_mul(GOLDEN) ^ w[1].wrapping_mul(SECOND);
        (h.rotate_left(29) ^ w[2]).wrapping_mul(GOLDEN)
    }
}

#[derive(Clone, Copy)]
struct Slot<W: Copy, V: Copy> {
    key: W,
    val: V,
}

pub(crate) struct PtrMap<K: Key, V: Copy> {
    tags: Vec<u8>,
    slots: Vec<MaybeUninit<Slot<K::Words, V>>>,
    shift: u32,
    epoch: u32,
    len: usize,
    limit: usize,
    floor: usize,
    _key: PhantomData<K>,
}

fn grow_limit(n: usize) -> usize {
    n / 8 * 6
}

const VACANT: u8 = 0;

static NEXT_EPOCH: AtomicU32 = AtomicU32::new(0);

impl<K: Key, V: Copy> PtrMap<K, V> {
    fn fresh(n: usize) -> Vec<MaybeUninit<Slot<K::Words, V>>> {
        let mut slots = Vec::with_capacity(n);
        unsafe {
            slots.set_len(n);
        }
        slots
    }

    #[inline(always)]
    fn place(&self, w: &K::Words) -> (usize, u8) {
        let h = K::hash(w);
        let index = usize::try_from(h >> self.shift).expect("usize is 64 bits wide");
        let tag = h.to_le_bytes()[0] | 0x80;
        (index, tag)
    }

    #[inline(always)]
    pub(crate) fn find(&self, k: K) -> Result<V, (usize, u8)> {
        let w = k.words();
        let mask = self.tags.len() - 1;
        let (mut i, tag) = self.place(&w);
        loop {
            let t = unsafe { *self.tags.get_unchecked(i) };
            if t == tag {
                let s = unsafe { self.slots.get_unchecked(i).assume_init_ref() };
                if s.key == w {
                    return Ok(s.val);
                }
            } else if t == VACANT {
                return Err((i, tag));
            }
            i = (i + 1) & mask;
        }
    }

    #[inline(always)]
    pub(crate) fn get(&self, k: &K) -> Option<V> {
        self.find(*k).ok()
    }

    #[inline(always)]
    pub(crate) fn insert_at(&mut self, at: (usize, u8), k: K, v: V) {
        self.tags[at.0] = at.1;
        self.slots[at.0].write(Slot {
            key: k.words(),
            val: v,
        });
        self.len += 1;
        if self.len > self.limit {
            self.grow();
        }
    }

    pub(crate) fn clear(&mut self) {
        Reset::reset(self);
    }

    #[inline(always)]
    pub(crate) fn epoch(&self) -> u32 {
        self.epoch
    }

    #[inline(always)]
    pub(crate) fn insert_found(&mut self, at: (usize, u8), epoch: u32, k: K, v: V) {
        if epoch == self.epoch && self.tags[at.0] == VACANT {
            self.insert_at(at, k, v);
        } else {
            self.insert(k, v);
        }
    }

    #[inline]
    pub(crate) fn insert(&mut self, k: K, v: V) {
        let w = k.words();
        let mask = self.tags.len() - 1;
        let (mut i, tag) = self.place(&w);
        loop {
            let t = self.tags[i];
            if t == tag {
                let s = unsafe { self.slots[i].assume_init_mut() };
                if s.key == w {
                    s.val = v;
                    return;
                }
            } else if t == VACANT {
                self.insert_at((i, tag), k, v);
                return;
            }
            i = (i + 1) & mask;
        }
    }

    #[cold]
    fn grow(&mut self) {
        let n = self.tags.len() * 2;
        let old_tags = std::mem::replace(&mut self.tags, vec![VACANT; n]);
        let old_slots = std::mem::replace(&mut self.slots, Self::fresh(n));
        self.shift -= 1;
        self.epoch = self.epoch.wrapping_add(1);
        self.limit = grow_limit(n);
        let mask = n - 1;
        for (t, s) in old_tags.into_iter().zip(old_slots) {
            if t == VACANT {
                continue;
            }
            let s = unsafe { s.assume_init() };
            let (mut i, tag) = self.place(&s.key);
            while self.tags[i] != VACANT {
                i = (i + 1) & mask;
            }
            self.tags[i] = tag;
            self.slots[i].write(s);
        }
    }

    fn resize_empty(&mut self, n: usize) {
        self.tags = vec![VACANT; n];
        self.slots = Self::fresh(n);
        self.shift = 64 - n.trailing_zeros();
        self.epoch = self.epoch.wrapping_add(1);
        self.limit = grow_limit(n);
        self.len = 0;
    }
}

impl<K: Key, V: Copy> Reset for PtrMap<K, V> {
    fn with_cap(cap: usize) -> Self {
        let n = (cap * 2).next_power_of_two().max(128);
        PtrMap {
            tags: vec![VACANT; n],
            slots: Self::fresh(n),
            shift: 64 - n.trailing_zeros(),
            epoch: NEXT_EPOCH.fetch_add(1 << 16, Ordering::Relaxed),
            len: 0,
            limit: grow_limit(n),
            floor: n,
            _key: PhantomData,
        }
    }

    fn reset(&mut self) {
        if self.len != 0 {
            self.tags.fill(VACANT);
            self.len = 0;
            self.epoch = self.epoch.wrapping_add(1);
        }
    }

    fn reset_shrink(&mut self) {
        let want = (self.len * 4).next_power_of_two().max(self.floor);
        if self.tags.len() >= want * 4 {
            self.resize_empty(want);
        } else {
            self.reset();
        }
    }
}

pub(crate) struct PtrSet<K: Key>(PtrMap<K, ()>);

impl<K: Key> PtrSet<K> {
    #[inline(always)]
    pub(crate) fn contains(&self, k: &K) -> bool {
        self.0.find(*k).is_ok()
    }

    #[inline]
    pub(crate) fn insert(&mut self, k: K) {
        self.0.insert(k, ());
    }

    pub(crate) fn clear(&mut self) {
        self.0.reset();
    }
}

impl<K: Key> Reset for PtrSet<K> {
    fn with_cap(cap: usize) -> Self {
        PtrSet(PtrMap::with_cap(cap))
    }

    fn reset(&mut self) {
        self.0.reset();
    }

    fn reset_shrink(&mut self) {
        self.0.reset_shrink();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fingerprint_collisions_preserve_distinct_keys() {
        let mut map: PtrMap<(u32, u32), u32> = Reset::with_cap(1);
        for i in 0..256 {
            map.insert((i, 7), i);
        }
        for i in 0..256 {
            assert_eq!(map.get(&(i, 7)), Some(i));
        }
        assert_eq!(map.get(&(256, 7)), None);
    }
}
