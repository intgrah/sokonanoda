// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::Reset;
use crate::checker::value::KeyTag;
use crate::term::hash::GOLDEN;
use crate::term::ptr::{ExprPtr, Id, LevelPtr, LevelsPtr, NamePtr};
use std::marker::PhantomData;
use std::mem::MaybeUninit;

pub(crate) trait Word: Copy {
    fn word(self) -> u64;
}

impl<T> Word for Id<'_, T> {
    #[inline(always)]
    fn word(self) -> u64 {
        self.addr() as u64
    }
}

impl<T> Word for Option<Id<'_, T>> {
    #[inline(always)]
    fn word(self) -> u64 {
        self.map_or(0, |id| id.addr() as u64)
    }
}

impl Word for ExprPtr<'_> {
    #[inline(always)]
    fn word(self) -> u64 {
        self.addr() as u64
    }
}

impl Word for NamePtr<'_> {
    #[inline(always)]
    fn word(self) -> u64 {
        self.get_hash()
    }
}

impl Word for LevelPtr<'_> {
    #[inline(always)]
    fn word(self) -> u64 {
        self.get_hash()
    }
}

impl Word for LevelsPtr<'_> {
    #[inline(always)]
    fn word(self) -> u64 {
        self.get_hash()
    }
}

impl Word for u32 {
    #[inline(always)]
    fn word(self) -> u64 {
        u64::from(self)
    }
}

impl Word for u64 {
    #[inline(always)]
    fn word(self) -> u64 {
        self
    }
}

impl Word for KeyTag {
    #[inline(always)]
    fn word(self) -> u64 {
        self.u64()
    }
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

impl<A: Word, B: Word> Key for (A, B) {
    type Words = [u64; 2];
    #[inline(always)]
    fn words(self) -> [u64; 2] {
        [self.0.word(), self.1.word()]
    }
    #[inline(always)]
    fn hash(w: &[u64; 2]) -> u64 {
        w[0].wrapping_mul(GOLDEN) ^ w[1].wrapping_mul(SECOND)
    }
}

impl<A: Word, B: Word, C: Word> Key for (A, B, C) {
    type Words = [u64; 3];
    #[inline(always)]
    fn words(self) -> [u64; 3] {
        [self.0.word(), self.1.word(), self.2.word()]
    }
    #[inline(always)]
    fn hash(w: &[u64; 3]) -> u64 {
        let h = w[0].wrapping_mul(GOLDEN) ^ w[1].wrapping_mul(SECOND);
        (h.rotate_left(29) ^ w[2]).wrapping_mul(GOLDEN)
    }
}

impl<A: Word, B: Word, C: Word, D: Word> Key for (A, B, C, D) {
    type Words = [u64; 4];
    #[inline(always)]
    fn words(self) -> [u64; 4] {
        [self.0.word(), self.1.word(), self.2.word(), self.3.word()]
    }
    #[inline(always)]
    fn hash(w: &[u64; 4]) -> u64 {
        let h = w[0].wrapping_mul(GOLDEN) ^ w[1].wrapping_mul(SECOND);
        let g = w[2].wrapping_mul(GOLDEN) ^ w[3].wrapping_mul(SECOND);
        (h.rotate_left(29) ^ g).wrapping_mul(GOLDEN)
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
    len: usize,
    floor: usize,
    _key: PhantomData<K>,
}

const VACANT: u8 = 0;

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
        let tag = ((h >> (self.shift - 7)) & 0x7f) as u8 | 0x80;
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
        if self.len * 8 > self.tags.len() * 6 {
            self.grow();
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
            len: 0,
            floor: n,
            _key: PhantomData,
        }
    }

    fn reset(&mut self) {
        if self.len != 0 {
            self.tags.fill(VACANT);
            self.len = 0;
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
