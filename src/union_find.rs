use crate::util::{new_fx_hash_map, FxHashMap};

pub(crate) struct UnionFind {
    index: FxHashMap<usize, u32>,
    parent: Vec<u32>,
    rank: Vec<u8>,
}

impl UnionFind {
    pub(crate) fn new() -> Self {
        Self { index: new_fx_hash_map(), parent: Vec::new(), rank: Vec::new() }
    }

    pub(crate) fn clear(&mut self) {
        self.index.clear();
        self.parent.clear();
        self.rank.clear();
    }

    pub(crate) fn capacity(&self) -> usize { self.index.capacity() }

    fn get_or_push(&mut self, a: usize) -> u32 {
        let next = u32::try_from(self.parent.len()).expect("equivalence class count exceeds u32");
        match self.index.entry(a) {
            std::collections::hash_map::Entry::Occupied(o) => *o.get(),
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert(next);
                self.parent.push(next);
                self.rank.push(0);
                next
            }
        }
    }

    fn root(&mut self, mut i: u32) -> u32 {
        loop {
            let p = self.parent[i as usize];
            if p == i {
                return i;
            }
            let g = self.parent[p as usize];
            self.parent[i as usize] = g;
            i = g;
        }
    }

    pub(crate) fn equiv(&mut self, a: usize, b: usize) -> bool {
        let Some(&ia) = self.index.get(&a) else { return false };
        let Some(&ib) = self.index.get(&b) else { return false };
        ia == ib || self.root(ia) == self.root(ib)
    }

    pub(crate) fn union(&mut self, a: usize, b: usize) {
        let ia = self.get_or_push(a);
        let ib = self.get_or_push(b);
        let ra = self.root(ia);
        let rb = self.root(ib);
        if ra == rb {
            return;
        }
        let (lo, hi) = if self.rank[ra as usize] < self.rank[rb as usize] { (ra, rb) } else { (rb, ra) };
        self.parent[lo as usize] = hi;
        if self.rank[lo as usize] == self.rank[hi as usize] {
            self.rank[hi as usize] += 1;
        }
    }
}
