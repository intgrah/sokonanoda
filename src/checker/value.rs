// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::term::hash::GOLDEN;
use crate::term::ptr::{BigUintPtr, ExprPtr, Id, LevelPtr, LevelsPtr, NamePtr, StringPtr};
use bumpalo::Bump;
use std::cell::{Cell, OnceCell};
use std::ptr::NonNull;

pub type V<'a> = &'a Value<'a>;
pub type E<'a> = &'a Env<'a>;
pub type C<'a> = &'a Ctx<'a>;
pub type S<'a> = &'a Spine<'a>;
pub(crate) type SpineArgs<'a> = smallvec::SmallVec<[V<'a>; 8]>;

#[derive(Debug, Clone, Copy)]
pub struct Closure<'a> {
    pub env: E<'a>,
    pub ctx: Option<C<'a>>,
    pub body: ExprPtr<'a>,
}

#[derive(Debug, Clone, Copy)]
pub enum RigidHead<'a> {
    BVar(u32, V<'a>),
    Axiom(NamePtr<'a>, LevelsPtr<'a>),
    Ctor(NamePtr<'a>, LevelsPtr<'a>),
    Recursor(NamePtr<'a>, LevelsPtr<'a>),
    QuotConst(NamePtr<'a>, LevelsPtr<'a>),
    Inductive(NamePtr<'a>, LevelsPtr<'a>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(crate) enum KeyTag {
    Sort = 1,
    NatLit,
    StrLit,
    BVar,
    Axiom,
    Ctor,
    Recursor,
    QuotConst,
    Inductive,
    Unfold,
    Lam,
    Pi,
    LevelSub,
    EmptySpine,
}

impl KeyTag {
    #[inline]
    pub(crate) fn u64(self) -> u64 {
        self as u64
    }

    #[inline]
    pub(crate) fn u128(self) -> u128 {
        self as u128
    }
}

impl RigidHead<'_> {
    #[inline]
    pub(crate) fn tag(self) -> KeyTag {
        match self {
            RigidHead::BVar(..) => KeyTag::BVar,
            RigidHead::Axiom(..) => KeyTag::Axiom,
            RigidHead::Ctor(..) => KeyTag::Ctor,
            RigidHead::Recursor(..) => KeyTag::Recursor,
            RigidHead::QuotConst(..) => KeyTag::QuotConst,
            RigidHead::Inductive(..) => KeyTag::Inductive,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct UnfoldHead<'a> {
    pub name: NamePtr<'a>,
    pub levels: LevelsPtr<'a>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Elim<'a> {
    ptr: NonNull<()>,
    _ph: std::marker::PhantomData<&'a ()>,
}

pub enum ElimView<'a> {
    App(V<'a>),
    Proj { ty_name: NamePtr<'a>, idx: u16 },
}

impl<'a> Elim<'a> {
    const IDX_SHIFT: u32 = 49;

    #[inline]
    pub fn app(v: V<'a>) -> Self {
        debug_assert!(Id::of(v).addr() & 1 == 0);
        Elim {
            ptr: NonNull::from(v).cast(),
            _ph: std::marker::PhantomData,
        }
    }

    #[inline]
    pub fn proj(ty_name: NamePtr<'a>, idx: u16) -> Self {
        let name = ty_name.into_raw();
        debug_assert!(
            name.addr().get() >> (Self::IDX_SHIFT - 1) == 0,
            "name address does not fit alongside a projection index"
        );
        let packed = name
            .as_ptr()
            .cast::<()>()
            .map_addr(|a| (a << 1) | 1 | (usize::from(idx) << Self::IDX_SHIFT));
        Elim {
            ptr: unsafe { NonNull::new_unchecked(packed) },
            _ph: std::marker::PhantomData,
        }
    }

    #[inline]
    pub fn is_app(self) -> bool {
        self.ptr.addr().get() & 1 == 0
    }

    #[inline]
    pub fn raw(self) -> u64 {
        self.ptr.addr().get() as u64
    }

    #[inline]
    pub fn view(self) -> ElimView<'a> {
        if self.is_app() {
            ElimView::App(unsafe { self.ptr.cast::<Value<'a>>().as_ref() })
        } else {
            let mask = (1usize << Self::IDX_SHIFT) - 1;
            let name = self.ptr.as_ptr().map_addr(|a| (a & mask) >> 1).cast();
            ElimView::Proj {
                ty_name: unsafe { NamePtr::from_raw(NonNull::new_unchecked(name)) },
                idx: (self.raw() >> Self::IDX_SHIFT) as u16,
            }
        }
    }
}

impl std::fmt::Debug for Elim<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.view() {
            ElimView::App(v) => write!(f, "App({v:p})"),
            ElimView::Proj { idx, .. } => write!(f, "Proj({idx})"),
        }
    }
}

#[derive(Debug)]
pub enum Value<'a> {
    Rigid {
        head: RigidHead<'a>,
        spine: S<'a>,
        canon: Cell<bool>,
        key: LazyKey,
    },
    Unfold {
        head: UnfoldHead<'a>,
        spine: S<'a>,
        head_value: &'a OnceCell<V<'a>>,
        forced: OnceCell<V<'a>>,
        canon: Cell<bool>,
        key: LazyKey,
    },
    Lam {
        binder_type: ExprPtr<'a>,
        body: Closure<'a>,
        canon: Cell<bool>,
        key: LazyKey,
    },
    Pi {
        domain: V<'a>,
        body: Closure<'a>,
        canon: Cell<bool>,
        key: LazyKey,
    },
    Sort {
        level: LevelPtr<'a>,
        key: LazyKey,
    },
    NatLit {
        ptr: BigUintPtr<'a>,
        key: LazyKey,
    },
    StrLit {
        ptr: StringPtr<'a>,
        key: LazyKey,
    },
}

#[inline]
pub fn kmix(a: u64, b: u64) -> u64 {
    (a ^ b).wrapping_mul(GOLDEN).rotate_left(29)
}

const KEY_PRESENT: u64 = 1 << 63;

#[inline]
fn seal((d, closed): (u64, bool)) -> u64 {
    (d & !1) | u64::from(closed) | KEY_PRESENT
}

#[derive(Debug, Default)]
pub struct LazyKey(Cell<u64>);

impl LazyKey {
    #[inline]
    fn get_or_seal(&self, compute: impl FnOnce() -> (u64, bool)) -> u64 {
        let k = self.0.get();
        if k & KEY_PRESENT != 0 {
            return k;
        }
        let k = seal(compute());
        self.0.set(k);
        k
    }
}

impl Value<'_> {
    #[inline]
    fn lazy_key(&self) -> &LazyKey {
        match self {
            Value::Rigid { key, .. }
            | Value::Unfold { key, .. }
            | Value::Lam { key, .. }
            | Value::Pi { key, .. }
            | Value::Sort { key, .. }
            | Value::NatLit { key, .. }
            | Value::StrLit { key, .. } => key,
        }
    }

    #[inline]
    pub fn digest(&self) -> u64 {
        self.lazy_key().get_or_seal(|| self.compute_key())
    }

    #[inline]
    pub fn is_canonical(&self) -> bool {
        match self {
            Value::Rigid { canon, .. }
            | Value::Unfold { canon, .. }
            | Value::Lam { canon, .. }
            | Value::Pi { canon, .. } => canon.get(),
            Value::Sort { .. } | Value::NatLit { .. } | Value::StrLit { .. } => true,
        }
    }

    #[inline]
    pub fn mark_canonical(&self) {
        match self {
            Value::Rigid { canon, .. }
            | Value::Unfold { canon, .. }
            | Value::Lam { canon, .. }
            | Value::Pi { canon, .. } => canon.set(true),
            _ => {}
        }
    }

    fn compute_key(&self) -> (u64, bool) {
        match self {
            Value::Rigid { head, spine, .. } => {
                let (h, c) = head_key(*head);
                (kmix(h, spine.key()), c && spine.is_closed())
            }
            Value::Unfold { head, spine, .. } => (
                kmix(
                    const_key(KeyTag::Unfold, head.name, head.levels),
                    spine.key(),
                ),
                spine.is_closed(),
            ),
            Value::Lam {
                binder_type, body, ..
            } => {
                let (b, c) = closure_key(body);
                let h = kmix(KeyTag::Lam.u64(), binder_type.addr() as u64);
                (kmix(h, b), c)
            }
            Value::Pi { domain, body, .. } => {
                let (b, c) = closure_key(body);
                (
                    kmix(kmix(KeyTag::Pi.u64(), domain.digest()), b),
                    c && domain.is_closed(),
                )
            }
            Value::Sort { level, .. } => (kmix(KeyTag::Sort.u64(), level.get_hash()), true),
            Value::NatLit { ptr, .. } => (kmix(KeyTag::NatLit.u64(), ptr.get_hash()), true),
            Value::StrLit { ptr, .. } => (kmix(KeyTag::StrLit.u64(), ptr.get_hash()), true),
        }
    }

    #[inline]
    pub fn is_closed(&self) -> bool {
        self.digest() & 1 == 1
    }
}

#[inline]
fn const_key(tag: KeyTag, n: NamePtr<'_>, ls: LevelsPtr<'_>) -> u64 {
    kmix(kmix(tag.u64(), n.get_hash()), ls.get_hash())
}

fn head_key(head: RigidHead<'_>) -> (u64, bool) {
    match head {
        RigidHead::BVar(lvl, ty) => (
            kmix(kmix(KeyTag::BVar.u64(), u64::from(lvl)), ty.digest()),
            false,
        ),
        RigidHead::Axiom(n, ls)
        | RigidHead::Ctor(n, ls)
        | RigidHead::Recursor(n, ls)
        | RigidHead::QuotConst(n, ls)
        | RigidHead::Inductive(n, ls) => (const_key(head.tag(), n, ls), true),
    }
}

fn env_slots_key(env: E<'_>, count: u16) -> (u64, bool) {
    let mut d = lsub_key(env.lsub());
    let mut closed = true;
    for i in 0..count {
        if let Some(v) = env.lookup(i) {
            d = kmix(kmix(d, u64::from(i)), v.digest());
            closed &= v.is_closed();
        }
    }
    (d, closed)
}

fn closure_key(clo: &Closure<'_>) -> (u64, bool) {
    let (e, c) = env_slots_key(clo.env, clo.body.num_loose_bvars().saturating_sub(1));
    (kmix(clo.body.addr() as u64, e), c && clo.ctx.is_none())
}

#[derive(Debug)]
pub struct LevelSub<'a> {
    pub ks: LevelsPtr<'a>,
    pub vs: LevelsPtr<'a>,
}

#[derive(Debug)]
pub enum Env<'a> {
    Nil {
        lsub: Option<&'a LevelSub<'a>>,
        hash: u64,
    },
    Cons {
        v: V<'a>,
        parent: E<'a>,
        lsub: Option<&'a LevelSub<'a>>,
        hash: u64,
        len: u32,
        prune: Cell<(u64, Option<E<'a>>)>,
    },
    Framed {
        mask: u64,
        slots: &'a [V<'a>],
        lsub: Option<&'a LevelSub<'a>>,
        hash: u64,
        len: u32,
        prune: Cell<(u64, Option<E<'a>>)>,
    },
    WideFramed {
        data: &'a WideFrame<'a>,
        lsub: Option<&'a LevelSub<'a>>,
        hash: u64,
        len: u32,
        prune: Cell<(u64, Option<E<'a>>)>,
    },
}

#[derive(Debug)]
pub struct WideFrame<'a> {
    pub indices: &'a [u16],
    pub slots: &'a [V<'a>],
}

impl<'a> WideFrame<'a> {
    #[cold]
    #[inline(never)]
    fn lookup(&self, idx: u16) -> Option<V<'a>> {
        self.indices.binary_search(&idx).ok().map(|i| self.slots[i])
    }
}

pub fn lsub_key(lsub: Option<&LevelSub<'_>>) -> u64 {
    match lsub {
        None => 1,
        Some(ls) => {
            kmix(
                kmix(KeyTag::LevelSub.u64(), ls.ks.get_hash()),
                ls.vs.get_hash(),
            ) | 1
        }
    }
}

impl<'a> Env<'a> {
    #[inline]
    pub fn get_hash(&self) -> u64 {
        match self {
            Env::Nil { hash, .. }
            | Env::Cons { hash, .. }
            | Env::Framed { hash, .. }
            | Env::WideFramed { hash, .. } => *hash,
        }
    }

    #[inline]
    pub(crate) fn len(&self) -> u32 {
        match self {
            Env::Nil { .. } => 0,
            Env::Cons { len, .. } | Env::Framed { len, .. } | Env::WideFramed { len, .. } => *len,
        }
    }

    #[inline]
    pub fn lsub(&self) -> Option<&'a LevelSub<'a>> {
        match self {
            Env::Nil { lsub, .. }
            | Env::Cons { lsub, .. }
            | Env::Framed { lsub, .. }
            | Env::WideFramed { lsub, .. } => *lsub,
        }
    }
}

#[derive(Debug)]
pub enum Ctx<'a> {
    Nil,
    Cons { ty: V<'a>, parent: C<'a> },
}

#[derive(Debug)]
pub enum Spine<'a> {
    Empty,
    Snoc {
        prev: S<'a>,
        elim: Elim<'a>,
        len: u32,
        canon: Cell<bool>,
        has_proj: bool,
        key: LazyKey,
    },
}

impl Spine<'_> {
    #[inline]
    pub fn is_canonical(&self) -> bool {
        match self {
            Spine::Empty => true,
            Spine::Snoc { canon, .. } => canon.get(),
        }
    }

    #[inline]
    pub fn mark_canonical(&self) {
        if let Spine::Snoc { canon, .. } = self {
            canon.set(true);
        }
    }

    #[inline]
    pub fn key(&self) -> u64 {
        let Spine::Snoc {
            prev, elim, key, ..
        } = self
        else {
            return seal((KeyTag::EmptySpine.u64(), true));
        };
        key.get_or_seal(|| match elim.view() {
            ElimView::App(v) => (
                kmix(prev.key(), v.digest()),
                prev.is_closed() && v.is_closed(),
            ),
            ElimView::Proj { ty_name, idx } => (
                kmix(
                    kmix(prev.key(), ty_name.get_hash()),
                    u64::from(idx) | (1 << 60),
                ),
                prev.is_closed(),
            ),
        })
    }

    #[inline]
    pub fn is_closed(&self) -> bool {
        self.key() & 1 == 1
    }
}

impl<'a> Env<'a> {
    #[inline]
    pub fn lookup(&self, mut idx: u16) -> Option<V<'a>> {
        let mut cur = self;
        loop {
            match cur {
                Env::Nil { .. } => return None,
                Env::Cons { v, parent, .. } => {
                    if idx == 0 {
                        return Some(*v);
                    }
                    idx -= 1;
                    cur = parent;
                }
                Env::Framed { mask, slots, .. } => {
                    if idx >= 64 || (mask >> idx) & 1 == 0 {
                        return None;
                    }
                    let below = mask & ((1u64 << idx) - 1);
                    return Some(slots[below.count_ones() as usize]);
                }
                Env::WideFramed { data, .. } => return data.lookup(idx),
            }
        }
    }
}

impl<'a> Closure<'a> {
    pub fn mk_eval(env: E<'a>, body: ExprPtr<'a>) -> Self {
        Closure {
            env,
            ctx: None,
            body,
        }
    }

    pub fn mk_infer(env: E<'a>, ctx: C<'a>, body: ExprPtr<'a>) -> Self {
        Closure {
            env,
            ctx: Some(ctx),
            body,
        }
    }
}

impl<'a> Ctx<'a> {
    pub fn lookup(&self, mut idx: u16) -> Option<V<'a>> {
        let mut cur = self;
        while let Ctx::Cons { ty, parent } = cur {
            if idx == 0 {
                return Some(*ty);
            }
            idx -= 1;
            cur = parent;
        }
        None
    }
}

impl<'a> Spine<'a> {
    #[inline]
    pub fn has_proj(&self) -> bool {
        match self {
            Spine::Empty => false,
            Spine::Snoc { has_proj, .. } => *has_proj,
        }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Spine::Empty)
    }

    #[inline]
    pub fn len(&self) -> u32 {
        match self {
            Spine::Empty => 0,
            Spine::Snoc { len, .. } => *len,
        }
    }
    #[inline]
    pub fn elims_rev(&'a self) -> ElimsRev<'a> {
        ElimsRev(self)
    }

    pub fn to_vec(&'a self) -> Vec<Elim<'a>> {
        let mut out = Vec::with_capacity(self.len() as usize);
        out.extend(self.elims_rev());
        out.reverse();
        out
    }

    pub fn get(&'a self, i: usize) -> Option<Elim<'a>> {
        let steps = (self.len() as usize).checked_sub(i + 1)?;
        self.elims_rev().nth(steps)
    }
}

pub struct ElimsRev<'a>(S<'a>);

impl<'a> Iterator for ElimsRev<'a> {
    type Item = Elim<'a>;

    #[inline]
    fn next(&mut self) -> Option<Elim<'a>> {
        let Spine::Snoc { prev, elim, .. } = self.0 else {
            return None;
        };
        self.0 = prev;
        Some(*elim)
    }
}

pub fn env_empty(arena: &Bump) -> E<'_> {
    arena.alloc(Env::Nil {
        lsub: None,
        hash: 0,
    })
}
pub fn env_extend<'a>(arena: &'a Bump, parent: E<'a>, v: V<'a>) -> E<'a> {
    let hash = parent
        .get_hash()
        .wrapping_mul(GOLDEN)
        .wrapping_add(Id::of(v).addr() as u64);
    arena.alloc(Env::Cons {
        v,
        parent,
        lsub: parent.lsub(),
        hash,
        len: parent.len() + 1,
        prune: Cell::new((0, None)),
    })
}
pub fn ctx_empty(arena: &Bump) -> C<'_> {
    arena.alloc(Ctx::Nil)
}
pub fn ctx_extend<'a>(arena: &'a Bump, parent: C<'a>, ty: V<'a>) -> C<'a> {
    arena.alloc(Ctx::Cons { ty, parent })
}
pub fn spine_empty(arena: &Bump) -> S<'_> {
    arena.alloc(Spine::Empty)
}
pub fn spine_snoc<'a>(arena: &'a Bump, prev: S<'a>, elim: Elim<'a>) -> S<'a> {
    arena.alloc(Spine::Snoc {
        prev,
        elim,
        len: prev.len() + 1,
        canon: Cell::new(false),
        has_proj: prev.has_proj() || !elim.is_app(),
        key: LazyKey::default(),
    })
}

pub fn mk_rigid<'a>(arena: &'a Bump, head: RigidHead<'a>, spine: S<'a>) -> V<'a> {
    arena.alloc(Value::Rigid {
        head,
        spine,
        canon: Cell::new(false),
        key: LazyKey::default(),
    })
}

pub fn mk_unfold<'a>(
    arena: &'a Bump,
    name: NamePtr<'a>,
    levels: LevelsPtr<'a>,
    spine: S<'a>,
    head_value: &'a OnceCell<V<'a>>,
) -> V<'a> {
    arena.alloc(Value::Unfold {
        head: UnfoldHead { name, levels },
        spine,
        head_value,
        forced: OnceCell::new(),
        canon: Cell::new(false),
        key: LazyKey::default(),
    })
}
pub fn mk_unfold_head_with_empty<'a>(
    arena: &'a Bump,
    name: NamePtr<'a>,
    levels: LevelsPtr<'a>,
    head_value: &'a OnceCell<V<'a>>,
    empty: S<'a>,
) -> V<'a> {
    let forced = OnceCell::new();
    if let Some(hv) = head_value.get() {
        let _ = forced.set(*hv);
    }
    arena.alloc(Value::Unfold {
        head: UnfoldHead { name, levels },
        spine: empty,
        head_value,
        forced,
        canon: Cell::new(false),
        key: LazyKey::default(),
    })
}
pub fn mk_lam<'a>(arena: &'a Bump, binder_type: ExprPtr<'a>, body: Closure<'a>) -> V<'a> {
    arena.alloc(Value::Lam {
        binder_type,
        body,
        canon: Cell::new(false),
        key: LazyKey::default(),
    })
}
pub fn mk_pi<'a>(arena: &'a Bump, domain: V<'a>, body: Closure<'a>) -> V<'a> {
    arena.alloc(Value::Pi {
        domain,
        body,
        canon: Cell::new(false),
        key: LazyKey::default(),
    })
}
pub fn mk_sort<'a>(arena: &'a Bump, level: LevelPtr<'a>) -> V<'a> {
    arena.alloc(Value::Sort {
        level,
        key: LazyKey::default(),
    })
}
pub fn mk_natlit<'a>(arena: &'a Bump, ptr: BigUintPtr<'a>) -> V<'a> {
    arena.alloc(Value::NatLit {
        ptr,
        key: LazyKey::default(),
    })
}
pub fn mk_strlit<'a>(arena: &'a Bump, ptr: StringPtr<'a>) -> V<'a> {
    arena.alloc(Value::StrLit {
        ptr,
        key: LazyKey::default(),
    })
}
pub fn mk_bvar_with_empty<'a>(arena: &'a Bump, level: u32, ty: V<'a>, empty: S<'a>) -> V<'a> {
    mk_rigid(arena, RigidHead::BVar(level, ty), empty)
}

const _: () = assert!(std::mem::size_of::<Value<'static>>() == 56);
const _: () = assert!(std::mem::size_of::<Spine<'static>>() == 32);

impl<'t> Spine<'t> {
    pub(crate) fn apps(&'t self) -> Option<SpineArgs<'t>> {
        let mut out = SpineArgs::with_capacity(self.len() as usize);
        for elim in self.elims_rev() {
            let ElimView::App(a) = elim.view() else {
                return None;
            };
            out.push(a);
        }
        out.reverse();
        Some(out)
    }
}

impl<'t> Value<'t> {
    pub(crate) fn as_inductive_app(&self) -> Option<(NamePtr<'t>, LevelsPtr<'t>, SpineArgs<'t>)> {
        match self {
            Value::Rigid {
                head: RigidHead::Inductive(n, ls),
                spine,
                ..
            } => {
                let args = spine.apps()?;
                Some((*n, *ls, args))
            }
            _ => None,
        }
    }

    pub(crate) fn as_ctor_app(&self) -> Option<(NamePtr<'t>, SpineArgs<'t>)> {
        match self {
            Value::Rigid {
                head: RigidHead::Ctor(name, _),
                spine,
                ..
            } => {
                let args = spine.apps()?;
                Some((*name, args))
            }
            _ => None,
        }
    }
}
