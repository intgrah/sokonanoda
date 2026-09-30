use crate::checker::cache::memo;
use crate::checker::tc::TypeChecker;
use crate::checker::value::{kmix, Closure, ElimView, KeyTag, RigidHead, Value, E, S, V};
use crate::term::ptr::{Id, LevelsPtr, NamePtr};

#[inline]
fn mix(a: u128, b: u128) -> u128 {
    (a ^ b)
        .wrapping_mul(0x9E37_79B9_7F4A_7C15_BF58_476D_1CE4_E5B9)
        .rotate_left(47)
}

fn head_key(tag: KeyTag, n: NamePtr<'_>, ls: LevelsPtr<'_>) -> u128 {
    mix(
        mix(tag.u128(), u128::from(n.get_hash())),
        u128::from(ls.get_hash()),
    )
}

const WHNF_ADMIT_THRESHOLD: u8 = 2;

const FAIL_CLOSURE: u8 = 1;
const FAIL_DEPTH: u8 = 7;

impl<'x, 't, 'p> TypeChecker<'x, 't, 'p> {
    #[inline]
    pub(super) fn note_whnf(&mut self, depth: u32, src: V<'t>, res: V<'t>, steps: u32) {
        if steps == 0 {
            return;
        }
        let closed = src.is_closed();
        let k = src.digest();
        if !closed {
            return;
        }
        let (fi, fb) = crate::checker::cache::tenure_slot(k as usize);
        if self.tc_cache.whnf_store_filter[fi] & fb != 0
            && self.tc_cache.whnf_store.contains_key(&k)
        {
            return;
        }
        let ai = crate::checker::cache::admit_slot(k);
        let seen = &mut self.tc_cache.whnf_admit[ai];
        if *seen < WHNF_ADMIT_THRESHOLD {
            *seen = seen.saturating_add(1);
            return;
        }
        let Ok((full, verified)) = self.global_key(src, depth) else {
            return;
        };
        if !verified {
            return;
        }
        let Some(hk) = Self::shallow_head_key(src) else {
            return;
        };
        let q = self.quote(0, res);
        let (hi, hb) = crate::checker::cache::tenure_slot(hk as usize);
        self.tc_cache.whnf_head_filter[hi] |= hb;
        self.tc_cache.whnf_store_filter[fi] |= fb;
        self.tc_cache.whnf_store.insert(k, (full, q));
    }

    #[inline]
    fn shallow_head_key(v: V<'t>) -> Option<u64> {
        let head = |tag: KeyTag, n: NamePtr<'t>, ls: LevelsPtr<'t>| {
            kmix(tag.u64(), kmix(n.get_hash(), ls.get_hash()))
        };
        let (h, spine) = match v {
            Value::Unfold { head: u, spine, .. } => {
                (head(KeyTag::Unfold, u.name, u.levels), *spine)
            }
            Value::Rigid {
                head: h @ (RigidHead::Recursor(n, ls) | RigidHead::QuotConst(n, ls)),
                spine,
                ..
            } => (head(h.tag(), *n, *ls), *spine),
            Value::Thunk { expr, .. } => {
                return Some(kmix(KeyTag::Thunk.u64(), expr.addr() as u64))
            }
            _ => return None,
        };
        Some(kmix(h, u64::from(spine.len())))
    }

    #[inline]
    pub(super) fn store_lookup(&mut self, depth: u32, v: V<'t>) -> Option<V<'t>> {
        let hk = Self::shallow_head_key(v)?;
        let (hi, hb) = crate::checker::cache::tenure_slot(hk as usize);
        if self.tc_cache.whnf_head_filter[hi] & hb == 0 {
            return None;
        }
        if !v.is_closed() {
            return None;
        }
        let k = v.digest();
        let (fi, fb) = crate::checker::cache::tenure_slot(k as usize);
        if self.tc_cache.whnf_store_filter[fi] & fb == 0 {
            return None;
        }
        let &(full, e) = self.tc_cache.whnf_store.get(&k)?;
        let (mine, verified) = self.global_key(v, depth).ok()?;
        if !verified || mine != full {
            return None;
        }
        let env = self.empty_env();
        Some(self.eval(depth, env, e))
    }

    fn global_key(&mut self, v: V<'t>, depth: u32) -> Result<(u128, bool), u8> {
        memo!(
            self.tc_cache.global_value_cache,
            (Id::of(v), depth),
            self.global_key_uncached(v, depth)
        )
    }

    fn global_key_uncached(&mut self, v: V<'t>, depth: u32) -> Result<(u128, bool), u8> {
        match v {
            Value::Sort { level, .. } => {
                Ok((mix(KeyTag::Sort.u128(), u128::from(level.get_hash())), true))
            }
            Value::NatLit { ptr, .. } => {
                Ok((mix(KeyTag::NatLit.u128(), u128::from(ptr.get_hash())), true))
            }
            Value::StrLit { ptr, .. } => {
                Ok((mix(KeyTag::StrLit.u128(), u128::from(ptr.get_hash())), true))
            }
            Value::Rigid { head, spine, .. } => {
                let (h, c) = match *head {
                    RigidHead::BVar(lvl, ty) => {
                        if lvl >= depth {
                            return Err(FAIL_DEPTH);
                        }
                        let (t, _) = self.global_key(ty, depth)?;
                        (
                            mix(mix(KeyTag::BVar.u128(), u128::from(depth - 1 - lvl)), t),
                            false,
                        )
                    }
                    RigidHead::Axiom(n, ls)
                    | RigidHead::Ctor(n, ls)
                    | RigidHead::Recursor(n, ls)
                    | RigidHead::QuotConst(n, ls)
                    | RigidHead::Inductive(n, ls) => (head_key(head.tag(), n, ls), true),
                };
                self.spine_key(h, c, spine, depth)
            }
            Value::Unfold { head, spine, .. } => {
                let h = head_key(KeyTag::Unfold, head.name, head.levels);
                self.spine_key(h, true, spine, depth)
            }
            Value::Lam {
                binder_type, body, ..
            } => {
                let h = mix(KeyTag::Lam.u128(), binder_type.addr() as u128);
                self.closure_key(h, body, depth)
            }
            Value::Pi { domain, body, .. } => {
                let (d, dc) = self.global_key(domain, depth)?;
                let (k, cc) = self.closure_key(mix(KeyTag::Pi.u128(), d), body, depth)?;
                Ok((k, dc && cc))
            }
            Value::Thunk { env, expr, .. } => {
                let acc = mix(KeyTag::Thunk.u128(), expr.addr() as u128);
                self.env_key(acc, true, env, depth, expr.num_loose_bvars())
            }
        }
    }

    fn closure_key(
        &mut self,
        tag: u128,
        clo: &Closure<'t>,
        depth: u32,
    ) -> Result<(u128, bool), u8> {
        if clo.ctx.is_some() {
            return Err(FAIL_CLOSURE);
        }
        let acc = mix(tag, clo.body.addr() as u128);
        self.env_key(
            acc,
            true,
            clo.env,
            depth,
            clo.body.num_loose_bvars().saturating_sub(1),
        )
    }

    fn env_key(
        &mut self,
        acc: u128,
        closed: bool,
        env: E<'t>,
        depth: u32,
        count: u16,
    ) -> Result<(u128, bool), u8> {
        let mut acc = acc;
        let mut closed = closed;
        if let Some(ls) = env.lsub() {
            acc = mix(
                mix(acc, u128::from(ls.ks.get_hash())),
                u128::from(ls.vs.get_hash()),
            );
        }
        for i in 0..count {
            if let Some(slot) = env.lookup(i) {
                let (k, c) = self.global_key(slot, depth)?;
                acc = mix(mix(acc, u128::from(i)), k);
                closed &= c;
            }
        }
        Ok((acc, closed))
    }

    fn spine_key(
        &mut self,
        head: u128,
        closed: bool,
        s: S<'t>,
        depth: u32,
    ) -> Result<(u128, bool), u8> {
        let mut acc = head;
        let mut closed = closed;
        for elim in s.to_vec() {
            acc = match elim.view() {
                ElimView::App(a) => {
                    let (k, c) = self.global_key(a, depth)?;
                    closed &= c;
                    mix(acc, k)
                }
                ElimView::Proj { ty_name, idx } => mix(
                    mix(acc, u128::from(ty_name.get_hash())),
                    u128::from(idx) | (1 << 60),
                ),
            };
        }
        Ok((acc, closed))
    }
}
