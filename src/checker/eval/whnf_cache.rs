use crate::checker::tc::TypeChecker;
use crate::checker::value::{self, Closure, ElimView, RigidHead, Value, E, S, V};
use crate::term::expr::Expr;
use crate::term::ptr::{LevelsPtr, NamePtr};

#[inline]
fn mix(a: u128, b: u128) -> u128 {
    (a ^ b)
        .wrapping_mul(0x9E37_79B9_7F4A_7C15_BF58_476D_1CE4_E5B9)
        .rotate_left(47)
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
        let (h, spine) = match v {
            Value::Unfold { head, spine, .. } => (
                value::kmix(
                    10,
                    value::kmix(head.name.get_hash(), head.levels.get_hash()),
                ),
                *spine,
            ),
            Value::Rigid {
                head: RigidHead::Recursor(n, ls),
                spine,
                ..
            } => (
                value::kmix(7, value::kmix(n.get_hash(), ls.get_hash())),
                *spine,
            ),
            Value::Rigid {
                head: RigidHead::QuotConst(n, ls),
                spine,
                ..
            } => (
                value::kmix(8, value::kmix(n.get_hash(), ls.get_hash())),
                *spine,
            ),
            Value::Thunk { expr, .. } => {
                return Some(value::kmix(
                    13,
                    expr.as_ref() as *const Expr<'t> as usize as u64,
                ))
            }
            _ => return None,
        };
        Some(value::kmix(h, u64::from(spine.len())))
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
        let addr = v as *const Value<'t> as usize;
        if let Some(&k) = self.tc_cache.global_value_cache.get(&(addr, depth)) {
            return k;
        }
        let r = self.global_key_uncached(v, depth);
        self.tc_cache.global_value_cache.insert((addr, depth), r);
        r
    }

    fn global_key_uncached(&mut self, v: V<'t>, depth: u32) -> Result<(u128, bool), u8> {
        match v {
            Value::Sort { level, .. } => Ok((mix(1, u128::from(level.get_hash())), true)),
            Value::NatLit { ptr, .. } => Ok((mix(2, u128::from(ptr.get_hash())), true)),
            Value::StrLit { ptr, .. } => Ok((mix(3, u128::from(ptr.get_hash())), true)),
            Value::Rigid { head, spine, .. } => {
                let (h, c) = match *head {
                    RigidHead::BVar(lvl, ty) => {
                        if lvl >= depth {
                            return Err(FAIL_DEPTH);
                        }
                        let (t, _) = self.global_key(ty, depth)?;
                        (mix(mix(4, u128::from(depth - 1 - lvl)), t), false)
                    }
                    RigidHead::Axiom(n, ls) => (self.head_key(5, n, ls), true),
                    RigidHead::Ctor(n, ls) => (self.head_key(6, n, ls), true),
                    RigidHead::Recursor(n, ls) => (self.head_key(7, n, ls), true),
                    RigidHead::QuotConst(n, ls) => (self.head_key(8, n, ls), true),
                    RigidHead::Inductive(n, ls) => (self.head_key(9, n, ls), true),
                };
                self.spine_key(h, c, spine, depth)
            }
            Value::Unfold { head, spine, .. } => {
                let h = self.head_key(10, head.name, head.levels);
                self.spine_key(h, true, spine, depth)
            }
            Value::Lam {
                binder_type, body, ..
            } => {
                let h = mix(11, binder_type.as_ref() as *const Expr<'t> as usize as u128);
                self.closure_key(h, body, depth)
            }
            Value::Pi { domain, body, .. } => {
                let h = 12;
                let (d, dc) = self.global_key(domain, depth)?;
                let (k, cc) = self.closure_key(mix(h, d), body, depth)?;
                Ok((k, dc && cc))
            }
            Value::Thunk { env, expr, .. } => {
                let acc = mix(13, expr.as_ref() as *const Expr<'t> as usize as u128);
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
        let acc = mix(tag, clo.body.as_ref() as *const Expr<'t> as usize as u128);
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

    fn head_key(&mut self, tag: u128, n: NamePtr<'t>, ls: LevelsPtr<'t>) -> u128 {
        mix(
            mix(tag, u128::from(n.get_hash())),
            u128::from(ls.get_hash()),
        )
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
