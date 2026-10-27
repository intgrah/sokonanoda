// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::{Reset, SESSION, SMALL};
use crate::checker::ptrmap::PtrMap;
use crate::term::expr::{FAR_VARS, NEAR_VARS};
use crate::term::hash::GOLDEN;
use crate::term::id::{BigId, ExprId, LevelId, LevelsId, NameId, StrId};

macro_rules! store_ids {
    ($($name:ident),*) => {
        $(
            #[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
            pub struct $name(u32);

            impl $name {
                #[inline(always)]
                fn index(self) -> usize {
                    self.0 as usize
                }

                #[inline(always)]
                pub(crate) fn raw(self) -> u32 {
                    self.0
                }
            }
        )*
    };
}

store_ids!(VId, EnvId, LsubId);

#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct CtxId(u32);

impl CtxId {
    #[inline(always)]
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[inline(always)]
fn at<T>(items: &[T], i: usize) -> &T {
    debug_assert!(i < items.len());
    unsafe { items.get_unchecked(i) }
}

#[inline(always)]
fn at_mut<T>(items: &mut [T], i: usize) -> &mut T {
    debug_assert!(i < items.len());
    unsafe { items.get_unchecked_mut(i) }
}

#[inline(always)]
pub(crate) fn pair(a: u32, b: u32) -> u64 {
    (u64::from(a) << 32) | u64::from(b)
}

const APP_ACTIVE: u32 = 1 << 31;

#[inline(always)]
fn next_id(len: usize) -> u32 {
    u32::try_from(len)
        .ok()
        .filter(|&i| i < APP_ACTIVE)
        .expect("value store exceeds 2^31 entries")
}

pub type V = VId;
pub type E = EnvId;
pub type C = CtxId;
pub type S = VId;
pub type CellId = VId;
pub(crate) type SpineArgs = smallvec::SmallVec<[V; 8]>;

pub(crate) const EMPTY_ENV: E = EnvId(0);
pub(crate) const DUMMY: V = VId(0);
pub(crate) const EMPTY_CTX: C = CtxId(0);

#[derive(Debug, Clone, Copy)]
pub struct Closure {
    pub env: E,
    pub ctx: Option<C>,
    pub body: ExprId,
    pub loose: u16,
}

#[derive(Debug, Clone, Copy)]
pub enum RigidHead {
    BVar(u32, V),
    Axiom(NameId, LevelsId),
    Ctor(NameId, LevelsId),
    Recursor(NameId, LevelsId),
    QuotConst(NameId, LevelsId),
    Inductive(NameId, LevelsId),
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

impl RigidHead {
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
pub struct UnfoldHead {
    pub name: NameId,
    pub levels: LevelsId,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Elim {
    App(V),
    Proj(NameId, u16),
}

pub enum ElimView {
    App(V),
    Proj { ty_name: NameId, idx: u16 },
}

impl Elim {
    #[inline]
    pub fn app(v: V) -> Self {
        Elim::App(v)
    }

    #[inline]
    pub fn proj(ty_name: NameId, idx: u16) -> Self {
        Elim::Proj(ty_name, idx)
    }

    #[inline]
    pub fn is_app(self) -> bool {
        matches!(self, Elim::App(_))
    }

    #[inline]
    pub fn view(self) -> ElimView {
        match self {
            Elim::App(v) => ElimView::App(v),
            Elim::Proj(ty_name, idx) => ElimView::Proj { ty_name, idx },
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Value {
    Rigid {
        head: RigidHead,
        spine: S,
    },
    Unfold {
        head: UnfoldHead,
        spine: S,
        head_value: CellId,
    },
    Lam {
        binder_type: ExprId,
        body: Closure,
    },
    Pi {
        domain: V,
        body: Closure,
    },
    Sort {
        level: LevelId,
    },
    NatLit {
        lit: BigId,
    },
    StrLit {
        lit: StrId,
    },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub(crate) enum VT {
    Dummy,
    Sort,
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
}

const SPINE_PROJ: u8 = 1;
const HAS_BVAR: u8 = 2;
const HEAD_ACTIVE: u8 = 4;
const IS_APP: u8 = 8;
const IS_PROJ: u8 = 16;
const SPINE_FLAGS: u8 = SPINE_PROJ | HAS_BVAR | HEAD_ACTIVE;

#[derive(Clone, Copy)]
struct VNode {
    kind: VT,
    flags: u8,
    loose: u16,
    a: u32,
    b: u32,
    c: u32,
    d: u32,
    step: u32,
    whnf: u32,
    ty: u32,
    key: u64,
}

const _: () = assert!(size_of::<VNode>() == 40);

#[inline(always)]
fn is_spine(n: &VNode) -> bool {
    n.flags & (IS_APP | IS_PROJ) != 0
}

#[inline(always)]
fn spine_head(v: V, n: &VNode) -> V {
    if is_spine(n) { VId(n.c) } else { v }
}

#[inline(always)]
fn spine_len(n: &VNode) -> u32 {
    if is_spine(n) { n.d } else { 0 }
}

const BLANK: VNode = VNode {
    kind: VT::Dummy,
    flags: 0,
    loose: 0,
    a: 0,
    b: 0,
    c: 0,
    d: 0,
    step: 0,
    whnf: 0,
    ty: 0,
    key: 0,
};

#[inline]
pub fn kmix(a: u64, b: u64) -> u64 {
    (a ^ b).wrapping_mul(GOLDEN).rotate_left(29)
}

const KEY_PRESENT: u64 = 1 << 63;

#[inline]
fn seal((d, closed): (u64, bool)) -> u64 {
    (d & !1) | u64::from(closed) | KEY_PRESENT
}

#[inline]
fn const_key(tag: KeyTag, n: NameId, ls: LevelsId) -> u64 {
    kmix(kmix(tag.u64(), u64::from(n.raw())), u64::from(ls.raw()))
}

#[derive(Debug, Clone, Copy)]
pub struct LevelSub {
    pub ks: LevelsId,
    pub vs: LevelsId,
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum EnvTag {
    Nil,
    Cons,
    Framed,
}

const NO_ENV: u32 = u32::MAX;

#[derive(Clone, Copy)]
struct EnvNode {
    mask: u64,
    a: u32,
    b: u32,
    len: u32,
    lsub: u32,
    tag: EnvTag,
    cut: u8,
}

const NIL_ENV_NODE: EnvNode = EnvNode {
    mask: 0,
    a: 0,
    b: NO_ENV,
    len: 0,
    lsub: 0,
    tag: EnvTag::Nil,
    cut: 0,
};

#[inline(always)]
fn lsub_code(lsub: Option<LsubId>) -> u32 {
    lsub.map_or(0, |l| l.0 + 1)
}

#[derive(Clone, Copy)]
pub(crate) enum EnvView {
    Nil,
    Cons {
        v: V,
        parent: E,
    },
    Framed {
        mask: u64,
        start: usize,
        cut: u32,
        rest: Option<E>,
    },
}

pub(crate) type SpineProjs = smallvec::SmallVec<[(usize, NameId, u16); 2]>;

pub(crate) const FAR: u64 = FAR_VARS;
pub(crate) const NEAR: u32 = NEAR_VARS as u32;

#[derive(Clone, Copy)]
struct CtxNode {
    ty: V,
    parent: C,
}

#[derive(Debug, Clone, Copy)]
pub enum Spine {
    Empty,
    Snoc { prev: S, elim: Elim },
}

pub(crate) struct Vals {
    nodes: Vec<VNode>,
    table: PtrMap<(u64, u64, u64), V>,
    apps: PtrMap<u64, u32>,
    memoized: Vec<V>,
    envs: Vec<EnvNode>,
    env_slots: Vec<V>,
    env_table: PtrMap<u64, E>,
    frames: PtrMap<u64, E>,
    nils: PtrMap<LsubId, E>,
    ctxs: Vec<CtxNode>,
    lsubs: Vec<LevelSub>,
}

impl Closure {
    pub fn mk_eval(env: E, body: ExprId, loose: u16) -> Self {
        Closure {
            env,
            ctx: None,
            body,
            loose,
        }
    }

    pub fn mk_infer(env: E, ctx: C, body: ExprId, loose: u16) -> Self {
        Closure {
            env,
            ctx: Some(ctx),
            body,
            loose,
        }
    }
}

impl Vals {
    pub(crate) fn new() -> Self {
        let mut vals = Vals {
            nodes: Vec::new(),
            table: Reset::with_cap(SESSION),
            apps: Reset::with_cap(SESSION),
            memoized: Vec::new(),
            envs: Vec::new(),
            env_slots: Vec::new(),
            env_table: Reset::with_cap(SESSION),
            frames: Reset::with_cap(SESSION),
            nils: Reset::with_cap(SMALL),
            ctxs: Vec::new(),
            lsubs: Vec::new(),
        };
        vals.clear();
        vals
    }

    pub(crate) fn clear(&mut self) {
        self.nodes.clear();
        self.table.reset_shrink();
        self.apps.reset_shrink();
        self.memoized.clear();
        self.envs.clear();
        self.env_slots.clear();
        self.env_table.reset_shrink();
        self.frames.reset_shrink();
        self.nils.reset();
        self.ctxs.clear();
        self.lsubs.clear();
        self.nodes.push(BLANK);
        self.envs.push(NIL_ENV_NODE);
        self.ctxs.push(CtxNode {
            ty: DUMMY,
            parent: EMPTY_CTX,
        });
    }

    pub(crate) fn clear_memos(&mut self) {
        for v in self.memoized.drain(..) {
            let n = at_mut(&mut self.nodes, v.index());
            n.step = 0;
            n.whnf = 0;
            n.ty = 0;
        }
    }

    #[inline(always)]
    fn memo_node(&mut self, v: V) -> &mut VNode {
        let n = at_mut(&mut self.nodes, v.index());
        if n.step | n.whnf | n.ty == 0 {
            self.memoized.push(v);
        }
        at_mut(&mut self.nodes, v.index())
    }

    pub(crate) fn reset(&mut self, keep: usize) {
        let held = self.nodes.capacity() * size_of::<VNode>()
            + self.envs.capacity() * size_of::<EnvNode>()
            + self.env_slots.capacity() * size_of::<V>()
            + self.ctxs.capacity() * size_of::<CtxNode>()
            + self.lsubs.capacity() * size_of::<LevelSub>();
        if held > keep {
            *self = Vals::new();
        } else {
            self.clear();
        }
    }

    pub(crate) fn used_bytes(&self) -> usize {
        self.nodes.len() * size_of::<VNode>()
            + self.envs.len() * size_of::<EnvNode>()
            + self.env_slots.len() * size_of::<V>()
            + self.ctxs.len() * size_of::<CtxNode>()
            + self.lsubs.len() * size_of::<LevelSub>()
    }

    #[inline(always)]
    fn node(&self, v: V) -> &VNode {
        at(&self.nodes, v.index())
    }

    #[inline(always)]
    pub(crate) fn val(&self, v: V) -> Value {
        let n = self.node(v);
        let head = |vals: &Self| {
            let h = spine_head(v, n);
            let hn = vals.node(h);
            (h, hn.a, hn.b)
        };
        let rigid = |head: RigidHead| Value::Rigid { head, spine: v };
        match n.kind {
            VT::Sort => Value::Sort {
                level: LevelId::from_raw(n.a),
            },
            VT::NatLit => Value::NatLit {
                lit: BigId::from_raw(n.a),
            },
            VT::StrLit => Value::StrLit {
                lit: StrId::from_raw(n.a),
            },
            VT::Lam => Value::Lam {
                binder_type: ExprId::from_raw(n.b),
                body: Closure {
                    env: EnvId(n.a),
                    ctx: None,
                    body: ExprId::from_raw(n.c),
                    loose: n.loose,
                },
            },
            VT::Pi => Value::Pi {
                domain: VId(n.a),
                body: Closure {
                    env: EnvId(n.b),
                    ctx: n.d.checked_sub(1).map(CtxId),
                    body: ExprId::from_raw(n.c),
                    loose: n.loose,
                },
            },
            VT::BVar => {
                let (_, a, b) = head(self);
                rigid(RigidHead::BVar(a, VId(b)))
            }
            VT::Axiom => {
                let (_, a, b) = head(self);
                rigid(RigidHead::Axiom(NameId::from_raw(a), LevelsId::from_raw(b)))
            }
            VT::Ctor => {
                let (_, a, b) = head(self);
                rigid(RigidHead::Ctor(NameId::from_raw(a), LevelsId::from_raw(b)))
            }
            VT::Recursor => {
                let (_, a, b) = head(self);
                rigid(RigidHead::Recursor(
                    NameId::from_raw(a),
                    LevelsId::from_raw(b),
                ))
            }
            VT::QuotConst => {
                let (_, a, b) = head(self);
                rigid(RigidHead::QuotConst(
                    NameId::from_raw(a),
                    LevelsId::from_raw(b),
                ))
            }
            VT::Inductive => {
                let (_, a, b) = head(self);
                rigid(RigidHead::Inductive(
                    NameId::from_raw(a),
                    LevelsId::from_raw(b),
                ))
            }
            VT::Unfold => {
                let (h, a, b) = head(self);
                Value::Unfold {
                    head: UnfoldHead {
                        name: NameId::from_raw(a),
                        levels: LevelsId::from_raw(b),
                    },
                    spine: v,
                    head_value: h,
                }
            }
            VT::Dummy => unreachable!("the reserved value node is never read"),
        }
    }

    #[inline(always)]
    pub(crate) fn spine(&self, s: S) -> Spine {
        let n = self.node(s);
        if n.flags & IS_APP != 0 {
            Spine::Snoc {
                prev: VId(n.a),
                elim: Elim::App(VId(n.b)),
            }
        } else if n.flags & IS_PROJ != 0 {
            Spine::Snoc {
                prev: VId(n.a),
                elim: Elim::Proj(NameId::from_raw(n.b), n.loose),
            }
        } else {
            Spine::Empty
        }
    }

    #[inline(always)]
    pub(crate) fn kind(&self, v: V) -> VT {
        self.node(v).kind
    }

    #[inline(always)]
    pub(crate) fn is_inert_rigid(&self, v: V) -> bool {
        let n = self.node(v);
        matches!(
            n.kind,
            VT::BVar | VT::Axiom | VT::Ctor | VT::Recursor | VT::QuotConst | VT::Inductive
        ) && n.flags & HEAD_ACTIVE == 0
    }

    #[inline(always)]
    pub(crate) fn is_neutral(&self, v: V) -> bool {
        matches!(
            self.node(v).kind,
            VT::BVar
                | VT::Axiom
                | VT::Ctor
                | VT::Recursor
                | VT::QuotConst
                | VT::Inductive
                | VT::Unfold
        )
    }

    #[inline(always)]
    pub(crate) fn head_name(&self, v: V) -> NameId {
        let n = self.node(v);
        debug_assert!(matches!(
            n.kind,
            VT::Axiom | VT::Ctor | VT::Recursor | VT::QuotConst | VT::Inductive | VT::Unfold
        ));
        NameId::from_raw(self.node(spine_head(v, n)).a)
    }

    #[inline(always)]
    pub(crate) fn is_head(&self, s: S) -> bool {
        !is_spine(self.node(s))
    }

    #[inline(always)]
    pub(crate) fn has_free_bvar(&self, v: V) -> bool {
        self.node(v).flags & HAS_BVAR != 0
    }

    #[inline(always)]
    pub(crate) fn lsub(&self, l: LsubId) -> LevelSub {
        *at(&self.lsubs, l.index())
    }

    #[inline(always)]
    pub(crate) fn step(&self, v: V) -> Option<V> {
        let s = self.node(v).step;
        (s != 0).then_some(VId(s))
    }

    #[inline(always)]
    pub(crate) fn whnf(&self, v: V) -> Option<V> {
        let w = self.node(v).whnf;
        (w != 0).then_some(VId(w))
    }

    #[inline(always)]
    pub(crate) fn set_whnf(&mut self, v: V, r: V) {
        self.memo_node(v).whnf = r.0;
    }

    #[inline(always)]
    pub(crate) fn ty(&self, v: V) -> Option<V> {
        let t = self.node(v).ty;
        (t != 0).then_some(VId(t))
    }

    #[inline(always)]
    pub(crate) fn set_ty(&mut self, v: V, r: V) {
        self.memo_node(v).ty = r.0;
    }

    #[inline(always)]
    pub(crate) fn set_step(&mut self, v: V, r: V) {
        let n = self.memo_node(v);
        if n.step == 0 {
            n.step = r.0;
        }
    }

    #[inline]
    pub fn digest(&mut self, v: V) -> u64 {
        let k = self.node(v).key;
        if k & KEY_PRESENT != 0 {
            return k;
        }
        let k = seal(self.compute_key(v));
        at_mut(&mut self.nodes, v.index()).key = k;
        k
    }

    #[inline]
    pub fn is_closed(&mut self, v: V) -> bool {
        self.digest(v) & 1 == 1
    }

    fn compute_key(&mut self, v: V) -> (u64, bool) {
        let n = *self.node(v);
        if n.flags & IS_APP != 0 {
            let (f, a) = (VId(n.a), VId(n.b));
            return (
                kmix(self.digest(f), self.digest(a)),
                self.is_closed(f) && self.is_closed(a),
            );
        }
        if n.flags & IS_PROJ != 0 {
            let s = VId(n.a);
            return (
                kmix(
                    kmix(self.digest(s), u64::from(n.b)),
                    u64::from(n.loose) | (1 << 60),
                ),
                self.is_closed(s),
            );
        }
        match n.kind {
            VT::Unfold => (
                const_key(
                    KeyTag::Unfold,
                    NameId::from_raw(n.a),
                    LevelsId::from_raw(n.b),
                ),
                true,
            ),
            _ => match self.val(v) {
                Value::Rigid { head, .. } => self.head_key(head),
                Value::Lam { binder_type, body } => {
                    let (b, c) = self.closure_key(&body);
                    let h = kmix(KeyTag::Lam.u64(), u64::from(binder_type.raw()));
                    (kmix(h, b), c)
                }
                Value::Pi { domain, body } => {
                    let (b, c) = self.closure_key(&body);
                    let d = self.digest(domain);
                    (
                        kmix(kmix(KeyTag::Pi.u64(), d), b),
                        c && self.is_closed(domain),
                    )
                }
                Value::Sort { level } => (kmix(KeyTag::Sort.u64(), u64::from(level.raw())), true),
                Value::NatLit { lit } => (kmix(KeyTag::NatLit.u64(), u64::from(lit.raw())), true),
                Value::StrLit { lit } => (kmix(KeyTag::StrLit.u64(), u64::from(lit.raw())), true),
                Value::Unfold { .. } => unreachable!(),
            },
        }
    }

    fn head_key(&mut self, head: RigidHead) -> (u64, bool) {
        match head {
            RigidHead::BVar(lvl, ty) => (
                kmix(kmix(KeyTag::BVar.u64(), u64::from(lvl)), self.digest(ty)),
                false,
            ),
            RigidHead::Axiom(n, ls)
            | RigidHead::Ctor(n, ls)
            | RigidHead::Recursor(n, ls)
            | RigidHead::QuotConst(n, ls)
            | RigidHead::Inductive(n, ls) => (const_key(head.tag(), n, ls), true),
        }
    }

    fn env_slots_key(&mut self, env: E, count: u16) -> (u64, bool) {
        let mut d = self.lsub_key(self.env_lsub(env));
        let mut closed = true;
        for i in 0..count {
            if let Some(v) = self.env_lookup(env, i) {
                d = kmix(kmix(d, u64::from(i)), self.digest(v));
                closed &= self.is_closed(v);
            }
        }
        (d, closed)
    }

    fn closure_key(&mut self, clo: &Closure) -> (u64, bool) {
        let (e, c) = self.env_slots_key(clo.env, clo.loose.saturating_sub(1));
        (kmix(u64::from(clo.body.raw()), e), c && clo.ctx.is_none())
    }

    pub fn lsub_key(&self, lsub: Option<LsubId>) -> u64 {
        match lsub {
            None => 1,
            Some(l) => {
                let ls = self.lsub(l);
                kmix(
                    kmix(KeyTag::LevelSub.u64(), u64::from(ls.ks.raw())),
                    u64::from(ls.vs.raw()),
                ) | 1
            }
        }
    }

    #[inline]
    pub(crate) fn env_len(&self, e: E) -> u32 {
        at(&self.envs, e.index()).len
    }

    #[inline]
    pub fn env_lsub(&self, e: E) -> Option<LsubId> {
        at(&self.envs, e.index()).lsub.checked_sub(1).map(LsubId)
    }

    #[inline]
    pub(crate) fn env_cons(&self, e: E) -> Option<(V, E)> {
        let n = at(&self.envs, e.index());
        (n.tag == EnvTag::Cons).then_some((VId(n.a), EnvId(n.b)))
    }

    #[inline]
    pub(crate) fn env_view(&self, e: E) -> EnvView {
        let n = at(&self.envs, e.index());
        match n.tag {
            EnvTag::Nil => EnvView::Nil,
            EnvTag::Cons => EnvView::Cons {
                v: VId(n.a),
                parent: EnvId(n.b),
            },
            EnvTag::Framed => EnvView::Framed {
                mask: n.mask,
                start: n.a as usize,
                cut: u32::from(n.cut),
                rest: (n.b != NO_ENV).then_some(EnvId(n.b)),
            },
        }
    }

    #[inline(always)]
    pub(crate) fn env_slot(&self, i: usize) -> V {
        *at(&self.env_slots, i)
    }

    #[inline(always)]
    pub(crate) fn env_slots_end(&self) -> usize {
        self.env_slots.len()
    }

    #[inline(always)]
    pub(crate) fn push_env_slot(&mut self, v: V) {
        self.env_slots.push(v);
    }

    #[inline(always)]
    pub(crate) fn drop_env_slots(&mut self, from: usize) {
        self.env_slots.truncate(from);
    }

    #[inline(always)]
    pub(crate) fn env_is_pruned(&self, e: E, mask: u64) -> bool {
        let n = at(&self.envs, e.index());
        n.mask & mask == n.mask
    }

    #[inline]
    pub fn env_lookup(&self, env: E, idx: u16) -> Option<V> {
        let mut idx = u32::from(idx);
        let mut n = at(&self.envs, env.index());
        loop {
            match n.tag {
                EnvTag::Cons => {
                    if idx == 0 {
                        return Some(VId(n.a));
                    }
                    idx -= 1;
                }
                EnvTag::Framed => {
                    let cut = u32::from(n.cut);
                    if idx < cut {
                        if (n.mask >> idx) & 1 == 0 {
                            return None;
                        }
                        let below = n.mask & ((1u64 << idx) - 1);
                        return Some(*at(
                            &self.env_slots,
                            n.a as usize + below.count_ones() as usize,
                        ));
                    }
                    if n.b == NO_ENV {
                        return None;
                    }
                    idx -= cut;
                }
                EnvTag::Nil => return None,
            }
            n = at(&self.envs, n.b as usize);
        }
    }

    pub fn ctx_lookup(&self, ctx: C, mut idx: u16) -> Option<V> {
        let mut cur = ctx;
        while cur != EMPTY_CTX {
            let n = at(&self.ctxs, cur.index());
            if idx == 0 {
                return Some(n.ty);
            }
            idx -= 1;
            cur = n.parent;
        }
        None
    }

    #[inline]
    pub fn has_proj(&self, s: S) -> bool {
        self.node(s).flags & SPINE_PROJ != 0
    }

    #[inline]
    pub fn spine_len(&self, s: S) -> u32 {
        spine_len(self.node(s))
    }

    #[inline]
    pub fn elims_rev(&self, s: S) -> ElimsRev<'_> {
        ElimsRev { vals: self, cur: s }
    }

    pub fn spine_to_vec(&self, s: S) -> smallvec::SmallVec<[Elim; 16]> {
        let mut out = smallvec::SmallVec::with_capacity(self.spine_len(s) as usize);
        out.extend(self.elims_rev(s));
        out.reverse();
        out
    }

    pub fn spine_get(&self, s: S, i: usize) -> Option<Elim> {
        let steps = (self.spine_len(s) as usize).checked_sub(i + 1)?;
        self.elims_rev(s).nth(steps)
    }

    pub(crate) fn spine_apps(&self, s: S) -> Option<SpineArgs> {
        (!self.has_proj(s)).then(|| self.spine_split(s).0)
    }

    pub(crate) fn spine_split(&self, s: S) -> (SpineArgs, SpineProjs) {
        let len = self.spine_len(s) as usize;
        let mut args: SpineArgs = smallvec::smallvec![DUMMY; len];
        let mut projs = SpineProjs::new();
        let mut i = len;
        let mut cur = self.node(s);
        while is_spine(cur) {
            if cur.flags & IS_APP != 0 {
                i -= 1;
                args[i] = VId(cur.b);
            } else {
                projs.push((i, NameId::from_raw(cur.b), cur.loose));
            }
            cur = self.node(VId(cur.a));
        }
        args.drain(..i);
        for p in &mut projs {
            p.0 -= i;
        }
        projs.reverse();
        (args, projs)
    }

    pub(crate) fn as_inductive_app(&self, v: V) -> Option<(NameId, LevelsId, SpineArgs)> {
        match self.val(v) {
            Value::Rigid {
                head: RigidHead::Inductive(n, ls),
                spine,
            } => Some((n, ls, self.spine_apps(spine)?)),
            _ => None,
        }
    }

    pub(crate) fn as_ctor_app(&self, v: V) -> Option<(NameId, SpineArgs)> {
        match self.val(v) {
            Value::Rigid {
                head: RigidHead::Ctor(name, _),
                spine,
            } => Some((name, self.spine_apps(spine)?)),
            _ => None,
        }
    }

    fn intern(&mut self, node: VNode) -> V {
        let w0 = node.kind as u64
            | (u64::from(node.flags) << 8)
            | (u64::from(node.loose) << 16)
            | (u64::from(node.a) << 32);
        let w1 = u64::from(node.b) | (u64::from(node.c) << 32);
        let key = (w0, w1, u64::from(node.d));
        match self.table.find(key) {
            Ok(v) => v,
            Err(slot) => {
                let id = self.push_node(node);
                self.table.insert_at(slot, key, id);
                id
            }
        }
    }

    fn push_node(&mut self, node: VNode) -> V {
        let id = VId(next_id(self.nodes.len()));
        self.nodes.push(node);
        id
    }

    pub(crate) fn mk_head(&mut self, head: RigidHead, active: bool) -> V {
        let (kind, a, b, flags) = match head {
            RigidHead::BVar(lvl, ty) => (VT::BVar, lvl, ty.0, HAS_BVAR),
            RigidHead::Axiom(n, ls) => (VT::Axiom, n.raw(), ls.raw(), 0),
            RigidHead::Ctor(n, ls) => (VT::Ctor, n.raw(), ls.raw(), 0),
            RigidHead::Recursor(n, ls) => (VT::Recursor, n.raw(), ls.raw(), 0),
            RigidHead::QuotConst(n, ls) => (VT::QuotConst, n.raw(), ls.raw(), 0),
            RigidHead::Inductive(n, ls) => (VT::Inductive, n.raw(), ls.raw(), 0),
        };
        let flags = if active { flags | HEAD_ACTIVE } else { flags };
        self.intern(VNode {
            kind,
            a,
            b,
            flags,
            ..BLANK
        })
    }

    pub(crate) fn mk_unfold_head(&mut self, name: NameId, levels: LevelsId, active: bool) -> V {
        self.intern(VNode {
            kind: VT::Unfold,
            a: name.raw(),
            b: levels.raw(),
            flags: if active { HEAD_ACTIVE } else { 0 },
            ..BLANK
        })
    }

    #[inline(always)]
    pub(crate) fn find_inert_app(&self, f: V, a: V) -> Option<V> {
        let v = self.apps.find(pair(f.0, a.0)).ok()?;
        (v & APP_ACTIVE == 0).then_some(VId(v))
    }

    #[inline(always)]
    pub(crate) fn app(&mut self, f: V, a: V) -> V {
        match self.apps.find(pair(f.0, a.0)) {
            Ok(v) => VId(v & !APP_ACTIVE),
            Err(slot) => self.app_new(slot, f, a),
        }
    }

    #[inline(never)]
    fn app_new(&mut self, slot: (usize, u8), f: V, a: V) -> V {
        let fl = *self.node(f);
        let flags = (fl.flags | (self.node(a).flags & HAS_BVAR)) & SPINE_FLAGS;
        let id = self.push_node(VNode {
            kind: fl.kind,
            flags: flags | IS_APP,
            a: f.0,
            b: a.0,
            c: spine_head(f, &fl).0,
            d: spine_len(&fl) + 1,
            ..BLANK
        });
        let active = if flags & HEAD_ACTIVE != 0 {
            APP_ACTIVE
        } else {
            0
        };
        self.apps.insert_at(slot, pair(f.0, a.0), id.0 | active);
        id
    }

    pub(crate) fn proj(&mut self, s: S, ty_name: NameId, idx: u16) -> V {
        let sl = *self.node(s);
        let id = self.intern(VNode {
            kind: sl.kind,
            flags: SPINE_PROJ | IS_PROJ | (sl.flags & SPINE_FLAGS),
            loose: idx,
            a: s.0,
            b: ty_name.raw(),
            c: spine_head(s, &sl).0,
            d: spine_len(&sl) + 1,
            ..BLANK
        });
        id
    }

    pub(crate) fn snoc(&mut self, prev: S, elim: Elim) -> V {
        match elim {
            Elim::App(a) => self.app(prev, a),
            Elim::Proj(ty_name, idx) => self.proj(prev, ty_name, idx),
        }
    }

    pub(crate) fn mk_lam(&mut self, binder_type: ExprId, body: Closure) -> V {
        debug_assert!(body.ctx.is_none());
        self.intern(VNode {
            kind: VT::Lam,
            loose: body.loose,
            a: body.env.0,
            b: binder_type.raw(),
            c: body.body.raw(),
            ..BLANK
        })
    }

    pub(crate) fn mk_pi(&mut self, domain: V, body: Closure) -> V {
        self.intern(VNode {
            kind: VT::Pi,
            loose: body.loose,
            a: domain.0,
            b: body.env.0,
            c: body.body.raw(),
            d: body.ctx.map_or(0, |c| c.0 + 1),
            ..BLANK
        })
    }

    pub(crate) fn mk_sort(&mut self, level: LevelId) -> V {
        self.intern(VNode {
            kind: VT::Sort,
            a: level.raw(),
            ..BLANK
        })
    }

    pub(crate) fn mk_natlit(&mut self, lit: BigId) -> V {
        self.intern(VNode {
            kind: VT::NatLit,
            a: lit.raw(),
            ..BLANK
        })
    }

    pub(crate) fn mk_strlit(&mut self, lit: StrId) -> V {
        self.intern(VNode {
            kind: VT::StrLit,
            a: lit.raw(),
            ..BLANK
        })
    }

    pub(crate) fn new_lsub(&mut self, ks: LevelsId, vs: LevelsId) -> LsubId {
        let id = LsubId(next_id(self.lsubs.len()));
        self.lsubs.push(LevelSub { ks, vs });
        id
    }

    pub(crate) fn env_nil(&mut self, lsub: Option<LsubId>) -> E {
        let Some(l) = lsub else {
            return EMPTY_ENV;
        };
        match self.nils.find(l) {
            Ok(e) => e,
            Err(slot) => {
                let id = EnvId(next_id(self.envs.len()));
                self.envs.push(EnvNode {
                    lsub: lsub_code(lsub),
                    ..NIL_ENV_NODE
                });
                self.nils.insert_at(slot, l, id);
                id
            }
        }
    }

    #[inline(always)]
    pub(crate) fn env_push(&mut self, parent: E, v: V) -> E {
        match self.env_table.find(pair(parent.0, v.0)) {
            Ok(e) => e,
            Err(slot) => self.env_new(slot, parent, v),
        }
    }

    #[inline(never)]
    fn env_new(&mut self, slot: (usize, u8), parent: E, v: V) -> E {
        let p = *at(&self.envs, parent.index());
        let id = EnvId(next_id(self.envs.len()));
        self.envs.push(EnvNode {
            mask: (p.mask << 1) | (p.mask & FAR) | 1,
            a: v.0,
            b: parent.0,
            len: p.len + 1,
            lsub: p.lsub,
            tag: EnvTag::Cons,
            ..NIL_ENV_NODE
        });
        self.env_table.insert_at(slot, pair(parent.0, v.0), id);
        id
    }

    pub(crate) fn intern_frame(
        &mut self,
        slots_hash: u64,
        near: u64,
        start: usize,
        cut: u32,
        rest: Option<E>,
        lsub: Option<LsubId>,
    ) -> (E, bool) {
        let mut hash = near.wrapping_mul(GOLDEN).wrapping_add(slots_hash);
        let (mask, cut, len) = match rest {
            Some(r) => {
                hash = (hash.rotate_left(29) ^ u64::from(r.0))
                    .wrapping_mul(GOLDEN)
                    .wrapping_add(u64::from(cut));
                (near | FAR, cut, cut + self.env_len(r))
            }
            None => (near, NEAR, 64 - near.leading_zeros()),
        };
        let count = (near & !FAR).count_ones() as usize;
        let found = self.frames.find(hash);
        if let Ok(e) = found {
            let n = at(&self.envs, e.index());
            let old = n.a as usize;
            if n.tag == EnvTag::Framed
                && n.mask == mask
                && u32::from(n.cut) == cut
                && n.b == rest.map_or(NO_ENV, |r| r.0)
                && n.lsub == lsub_code(lsub)
                && self.env_slots[old..old + count] == self.env_slots[start..start + count]
            {
                return (e, false);
            }
        }
        let id = EnvId(next_id(self.envs.len()));
        self.envs.push(EnvNode {
            mask,
            a: u32::try_from(start).expect("env slot store exceeds u32"),
            b: rest.map_or(NO_ENV, |r| r.0),
            len,
            lsub: lsub_code(lsub),
            tag: EnvTag::Framed,
            cut: u8::try_from(cut).expect("a frame spans at most 63 positions"),
            ..NIL_ENV_NODE
        });
        if let Err(vacant) = found {
            self.frames.insert_at(vacant, hash, id);
        }
        (id, true)
    }

    pub(crate) fn ctx_extend(&mut self, parent: C, ty: V) -> C {
        let id = CtxId(next_id(self.ctxs.len()));
        self.ctxs.push(CtxNode { ty, parent });
        id
    }
}

pub struct ElimsRev<'a> {
    vals: &'a Vals,
    cur: S,
}

impl Iterator for ElimsRev<'_> {
    type Item = Elim;

    #[inline]
    fn next(&mut self) -> Option<Elim> {
        let Spine::Snoc { prev, elim, .. } = self.vals.spine(self.cur) else {
            return None;
        };
        self.cur = prev;
        Some(elim)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::id::ZERO;

    #[test]
    fn extending_sparse_environment_keeps_far_dependencies() {
        let mut vals = Vals::new();
        let v = vals.mk_sort(ZERO);
        vals.push_env_slot(v);
        let (env, _) = vals.intern_frame(u64::from(v.raw()), 1 << 62, 0, NEAR, None, None);
        let env = vals.env_push(env, v);
        let env = vals.env_push(env, v);
        assert!(vals.env_is_pruned(env, FAR | 3));
        assert!(!vals.env_is_pruned(env, 3));
    }
}
