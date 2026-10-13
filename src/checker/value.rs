// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::{Reset, SESSION, SMALL};
use crate::checker::ptrmap::PtrMap;
use crate::term::expr::FAR_VARS;
use crate::term::hash::GOLDEN;
use crate::term::id::{BigId, ExprId, LevelId, LevelsId, NameId, StrId};

macro_rules! store_ids {
    ($($name:ident),*) => {
        $(
            #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
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

store_ids!(VId, EnvId, CtxId, LsubId);

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
fn next_id(len: usize) -> u32 {
    u32::try_from(len).expect("value store exceeds u32")
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
enum VT {
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
    App,
    Proj,
    Lam,
    Pi,
}

const SPINE_PROJ: u8 = 1;
const HAS_BVAR: u8 = 2;
const HEAD_ACTIVE: u8 = 4;

#[derive(Clone, Copy)]
struct VNode {
    t: VT,
    flags: u8,
    loose: u16,
    a: u32,
    b: u32,
    c: u32,
    d: u32,
    h: V,
    n: u32,
    step: u32,
    whnf: u32,
    ty: u32,
}

const BLANK: VNode = VNode {
    t: VT::Dummy,
    flags: 0,
    loose: 0,
    a: 0,
    b: 0,
    c: 0,
    d: 0,
    h: VId(0),
    n: 0,
    step: 0,
    whnf: 0,
    ty: 0,
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

const NO_ENV: u32 = u32::MAX;

#[derive(Clone, Copy)]
struct EnvNode {
    parent: u32,
    up: [u32; 3],
    val: V,
    vals: [V; 3],
    len: u32,
    lsub: Option<LsubId>,
}

const NIL_ENV_NODE: EnvNode = EnvNode {
    parent: NO_ENV,
    up: [NO_ENV; 3],
    val: DUMMY,
    vals: [DUMMY; 3],
    len: 0,
    lsub: None,
};

pub(crate) const FAR: u64 = FAR_VARS;

#[derive(Debug, Clone, Copy)]
pub enum Ctx {
    Nil,
    Cons { ty: V, parent: C },
}

#[derive(Debug, Clone, Copy)]
pub enum Spine {
    Empty,
    Snoc { prev: S, elim: Elim },
}

pub(crate) struct Vals {
    nodes: Vec<VNode>,
    keys: Vec<u64>,
    table: PtrMap<(u64, u64, u64), V>,
    apps: PtrMap<(V, V), V>,
    envs: Vec<EnvNode>,
    env_table: PtrMap<(E, V), E>,
    nils: PtrMap<LsubId, E>,
    ctxs: Vec<Ctx>,
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
            keys: Vec::new(),
            table: Reset::with_cap(SESSION),
            apps: Reset::with_cap(SESSION),
            envs: Vec::new(),
            env_table: Reset::with_cap(SESSION),
            nils: Reset::with_cap(SMALL),
            ctxs: Vec::new(),
            lsubs: Vec::new(),
        };
        vals.clear();
        vals
    }

    pub(crate) fn clear(&mut self) {
        self.nodes.clear();
        self.keys.clear();
        self.table.reset_shrink();
        self.apps.reset_shrink();
        self.envs.clear();
        self.env_table.reset_shrink();
        self.nils.reset();
        self.ctxs.clear();
        self.lsubs.clear();
        self.nodes.push(BLANK);
        self.keys.push(0);
        self.envs.push(NIL_ENV_NODE);
        self.ctxs.push(Ctx::Nil);
    }

    pub(crate) fn clear_memos(&mut self) {
        for n in &mut self.nodes {
            n.step = 0;
            n.whnf = 0;
            n.ty = 0;
        }
    }

    pub(crate) fn reset(&mut self, keep: usize) {
        let held = self.nodes.capacity() * size_of::<VNode>()
            + self.keys.capacity() * size_of::<u64>()
            + self.envs.capacity() * size_of::<EnvNode>()
            + self.ctxs.capacity() * size_of::<Ctx>()
            + self.lsubs.capacity() * size_of::<LevelSub>();
        if held > keep {
            *self = Vals::new();
        } else {
            self.clear();
        }
    }

    pub(crate) fn used_bytes(&self) -> usize {
        self.nodes.len() * (size_of::<VNode>() + size_of::<u64>())
            + self.envs.len() * size_of::<EnvNode>()
            + self.ctxs.len() * size_of::<Ctx>()
            + self.lsubs.len() * size_of::<LevelSub>()
    }

    #[inline(always)]
    fn node(&self, v: V) -> &VNode {
        at(&self.nodes, v.index())
    }

    #[inline(always)]
    pub(crate) fn val(&self, v: V) -> Value {
        let n = self.node(v);
        match n.t {
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
            VT::Dummy => unreachable!("the blank value is never read"),
            _ => {
                let h = self.node(n.h);
                let name = NameId::from_raw(h.a);
                let levels = LevelsId::from_raw(h.b);
                let head = match h.t {
                    VT::BVar => RigidHead::BVar(h.a, VId(h.b)),
                    VT::Axiom => RigidHead::Axiom(name, levels),
                    VT::Ctor => RigidHead::Ctor(name, levels),
                    VT::Recursor => RigidHead::Recursor(name, levels),
                    VT::QuotConst => RigidHead::QuotConst(name, levels),
                    VT::Inductive => RigidHead::Inductive(name, levels),
                    VT::Unfold => {
                        return Value::Unfold {
                            head: UnfoldHead { name, levels },
                            spine: v,
                            head_value: n.h,
                        };
                    }
                    _ => unreachable!("a spine head is a rigid or unfold head"),
                };
                Value::Rigid { head, spine: v }
            }
        }
    }

    #[inline(always)]
    pub(crate) fn spine(&self, s: S) -> Spine {
        let n = self.node(s);
        match n.t {
            VT::App => Spine::Snoc {
                prev: VId(n.a),
                elim: Elim::App(VId(n.b)),
            },
            VT::Proj => Spine::Snoc {
                prev: VId(n.a),
                elim: Elim::Proj(NameId::from_raw(n.c), n.b as u16),
            },
            _ => Spine::Empty,
        }
    }

    #[inline(always)]
    pub(crate) fn is_head(&self, s: S) -> bool {
        self.node(s).n == 0
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
        at_mut(&mut self.nodes, v.index()).whnf = r.0;
    }

    #[inline(always)]
    pub(crate) fn ty(&self, v: V) -> Option<V> {
        let t = self.node(v).ty;
        (t != 0).then_some(VId(t))
    }

    #[inline(always)]
    pub(crate) fn set_ty(&mut self, v: V, r: V) {
        at_mut(&mut self.nodes, v.index()).ty = r.0;
    }

    #[inline(always)]
    pub(crate) fn set_step(&mut self, v: V, r: V) {
        let n = at_mut(&mut self.nodes, v.index());
        if n.step == 0 {
            n.step = r.0;
        }
    }

    #[inline]
    pub fn digest(&mut self, v: V) -> u64 {
        let k = *at(&self.keys, v.index());
        if k & KEY_PRESENT != 0 {
            return k;
        }
        let k = seal(self.compute_key(v));
        *at_mut(&mut self.keys, v.index()) = k;
        k
    }

    #[inline]
    pub fn is_closed(&mut self, v: V) -> bool {
        self.digest(v) & 1 == 1
    }

    fn compute_key(&mut self, v: V) -> (u64, bool) {
        let n = *self.node(v);
        match n.t {
            VT::App => {
                let (f, a) = (VId(n.a), VId(n.b));
                (kmix(self.digest(f), self.digest(a)), self.is_closed(f) && self.is_closed(a))
            }
            VT::Proj => {
                let s = VId(n.a);
                (
                    kmix(kmix(self.digest(s), u64::from(n.c)), u64::from(n.b) | (1 << 60)),
                    self.is_closed(s),
                )
            }
            VT::Unfold => (
                const_key(KeyTag::Unfold, NameId::from_raw(n.a), LevelsId::from_raw(n.b)),
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
        at(&self.envs, e.index()).lsub
    }

    #[inline]
    pub(crate) fn env_cons(&self, e: E) -> Option<(V, E)> {
        let n = at(&self.envs, e.index());
        (n.parent != NO_ENV).then_some((n.val, EnvId(n.parent)))
    }

    #[inline]
    pub fn env_lookup(&self, env: E, idx: u16) -> Option<V> {
        let mut i = u32::from(idx);
        let mut cur = env;
        loop {
            let n = at(&self.envs, cur.index());
            if i >= n.len {
                return None;
            }
            let v = match i {
                0 => n.val,
                1..=3 => n.vals[i as usize - 1],
                _ => {
                    cur = EnvId(n.up[2]);
                    i -= 4;
                    continue;
                }
            };
            return (v != DUMMY).then_some(v);
        }
    }

    pub fn ctx_lookup(&self, ctx: C, mut idx: u16) -> Option<V> {
        let mut cur = ctx;
        while let Ctx::Cons { ty, parent } = *at(&self.ctxs, cur.index()) {
            if idx == 0 {
                return Some(ty);
            }
            idx -= 1;
            cur = parent;
        }
        None
    }

    #[inline]
    pub fn has_proj(&self, s: S) -> bool {
        self.node(s).flags & SPINE_PROJ != 0
    }

    #[inline]
    pub fn spine_len(&self, s: S) -> u32 {
        self.node(s).n
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
        if self.has_proj(s) {
            return None;
        }
        let mut out = SpineArgs::with_capacity(self.spine_len(s) as usize);
        let mut cur = self.node(s);
        while cur.t == VT::App {
            out.push(VId(cur.b));
            cur = self.node(VId(cur.a));
        }
        out.reverse();
        Some(out)
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
        let key = (
            node.t as u64 | (u64::from(node.a) << 8),
            u64::from(node.b) | (u64::from(node.c) << 32),
            u64::from(node.d) | (u64::from(node.loose) << 32),
        );
        match self.table.find(key) {
            Ok(v) => v,
            Err(slot) => {
                let id = self.push_node(node);
                if node.n == 0 && node.t != VT::Lam && node.t != VT::Pi {
                    at_mut(&mut self.nodes, id.index()).h = id;
                }
                self.table.insert_at(slot, key, id);
                id
            }
        }
    }

    fn push_node(&mut self, node: VNode) -> V {
        let id = VId(next_id(self.nodes.len()));
        self.nodes.push(node);
        self.keys.push(0);
        id
    }

    pub(crate) fn mk_head(&mut self, head: RigidHead, active: bool) -> V {
        let (t, a, b, flags) = match head {
            RigidHead::BVar(lvl, ty) => (VT::BVar, lvl, ty.0, HAS_BVAR),
            RigidHead::Axiom(n, ls) => (VT::Axiom, n.raw(), ls.raw(), 0),
            RigidHead::Ctor(n, ls) => (VT::Ctor, n.raw(), ls.raw(), 0),
            RigidHead::Recursor(n, ls) => (VT::Recursor, n.raw(), ls.raw(), 0),
            RigidHead::QuotConst(n, ls) => (VT::QuotConst, n.raw(), ls.raw(), 0),
            RigidHead::Inductive(n, ls) => (VT::Inductive, n.raw(), ls.raw(), 0),
        };
        let flags = if active { flags | HEAD_ACTIVE } else { flags };
        self.intern(VNode {
            t,
            a,
            b,
            flags,
            ..BLANK
        })
    }

    pub(crate) fn mk_unfold_head(&mut self, name: NameId, levels: LevelsId, active: bool) -> V {
        self.intern(VNode {
            t: VT::Unfold,
            a: name.raw(),
            b: levels.raw(),
            flags: if active { HEAD_ACTIVE } else { 0 },
            ..BLANK
        })
    }

    #[inline(always)]
    pub(crate) fn find_inert_app(&self, f: V, a: V) -> Option<V> {
        let v = self.apps.find((f, a)).ok()?;
        (self.node(v).flags & HEAD_ACTIVE == 0).then_some(v)
    }

    #[inline(always)]
    pub(crate) fn app(&mut self, f: V, a: V) -> V {
        match self.apps.find((f, a)) {
            Ok(v) => v,
            Err(slot) => self.app_new(slot, f, a),
        }
    }

    #[inline(never)]
    fn app_new(&mut self, slot: (usize, u8), f: V, a: V) -> V {
        let fl = *self.node(f);
        let flags = (fl.flags | (self.node(a).flags & HAS_BVAR)) & (SPINE_PROJ | HAS_BVAR | HEAD_ACTIVE);
        let id = self.push_node(VNode {
            t: VT::App,
            flags,
            a: f.0,
            b: a.0,
            h: fl.h,
            n: fl.n + 1,
            ..BLANK
        });
        self.apps.insert_at(slot, (f, a), id);
        id
    }

    pub(crate) fn proj(&mut self, s: S, ty_name: NameId, idx: u16) -> V {
        let sl = *self.node(s);
        let id = self.intern(VNode {
            t: VT::Proj,
            flags: SPINE_PROJ | (sl.flags & (HAS_BVAR | HEAD_ACTIVE)),
            a: s.0,
            b: u32::from(idx),
            c: ty_name.raw(),
            h: sl.h,
            n: sl.n + 1,
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
            t: VT::Lam,
            loose: body.loose,
            a: body.env.0,
            b: binder_type.raw(),
            c: body.body.raw(),
            ..BLANK
        })
    }

    pub(crate) fn mk_pi(&mut self, domain: V, body: Closure) -> V {
        self.intern(VNode {
            t: VT::Pi,
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
            t: VT::Sort,
            a: level.raw(),
            ..BLANK
        })
    }

    pub(crate) fn mk_natlit(&mut self, lit: BigId) -> V {
        self.intern(VNode {
            t: VT::NatLit,
            a: lit.raw(),
            ..BLANK
        })
    }

    pub(crate) fn mk_strlit(&mut self, lit: StrId) -> V {
        self.intern(VNode {
            t: VT::StrLit,
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
                self.envs.push(EnvNode { lsub, ..NIL_ENV_NODE });
                self.nils.insert_at(slot, l, id);
                id
            }
        }
    }

    #[inline(always)]
    pub(crate) fn env_push(&mut self, parent: E, v: V) -> E {
        match self.env_table.find((parent, v)) {
            Ok(e) => e,
            Err(slot) => self.env_new(slot, parent, v),
        }
    }

    #[inline(never)]
    fn env_new(&mut self, slot: (usize, u8), parent: E, v: V) -> E {
        let p = *at(&self.envs, parent.index());
        let id = EnvId(next_id(self.envs.len()));
        self.envs.push(EnvNode {
            parent: parent.0,
            up: [p.parent, p.up[0], p.up[1]],
            val: v,
            vals: [p.val, p.vals[0], p.vals[1]],
            len: p.len + 1,
            lsub: p.lsub,
        });
        self.env_table.insert_at(slot, (parent, v), id);
        id
    }

    pub(crate) fn ctx_extend(&mut self, parent: C, ty: V) -> C {
        let id = CtxId(next_id(self.ctxs.len()));
        self.ctxs.push(Ctx::Cons { ty, parent });
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
