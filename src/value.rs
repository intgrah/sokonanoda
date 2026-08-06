use crate::expr::BinderStyle;
use crate::util::{BigUintPtr, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};
use bumpalo::Bump;
use std::cell::{Cell, OnceCell};

pub type V<'a> = &'a Value<'a>;
pub type E<'a> = &'a Env<'a>;
pub type C<'a> = &'a Ctx<'a>;
pub type S<'a> = &'a Spine<'a>;

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

#[derive(Debug, Clone, Copy)]
pub struct UnfoldHead<'a> {
    pub name: NamePtr<'a>,
    pub levels: LevelsPtr<'a>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Elim<'a> {
    bits: u64,
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
        let addr = v as *const Value<'a> as usize as u64;
        debug_assert!(addr & 1 == 0);
        Elim { bits: addr, _ph: std::marker::PhantomData }
    }

    #[inline]
    pub fn proj(ty_name: NamePtr<'a>, idx: u16) -> Self {
        let addr = ty_name.get_hash();
        debug_assert!(addr >> (Self::IDX_SHIFT - 1) == 0, "name address does not fit alongside a projection index");
        Elim {
            bits: (addr << 1) | 1 | (u64::from(idx) << Self::IDX_SHIFT),
            _ph: std::marker::PhantomData,
        }
    }

    #[inline]
    pub fn is_app(self) -> bool { self.bits & 1 == 0 }

    #[inline]
    pub fn raw(self) -> u64 { self.bits }

    #[inline]
    pub fn view(self) -> ElimView<'a> {
        if self.is_app() {
            let p = self.bits as usize as *const Value<'a>;
            ElimView::App(unsafe { &*p })
        } else {
            let mask = (1u64 << Self::IDX_SHIFT) - 1;
            let addr = (self.bits & mask) >> 1;
            ElimView::Proj {
                ty_name: NamePtr::from_raw_hash(addr),
                idx: (self.bits >> Self::IDX_SHIFT) as u16,
            }
        }
    }
}

impl<'a> std::fmt::Debug for Elim<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.view() {
            ElimView::App(v) => write!(f, "App({:p})", v),
            ElimView::Proj { idx, .. } => write!(f, "Proj({})", idx),
        }
    }
}

#[derive(Debug)]
pub enum Value<'a> {
    Rigid {
        head: RigidHead<'a>,
        spine: S<'a>,
        canon: Cell<bool>,
        key: Cell<u64>,
    },
    Unfold {
        head: UnfoldHead<'a>,
        spine: S<'a>,
        head_value: &'a OnceCell<V<'a>>,
        forced: OnceCell<V<'a>>,
        canon: Cell<bool>,
        key: Cell<u64>,
    },
    Lam {
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: Closure<'a>,
        canon: Cell<bool>,
        key: Cell<u64>,
    },
    Pi {
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        domain: V<'a>,
        body: Closure<'a>,
        canon: Cell<bool>,
        key: Cell<u64>,
    },
    Sort {
        level: LevelPtr<'a>,
        key: Cell<u64>,
    },
    NatLit {
        ptr: BigUintPtr<'a>,
        key: Cell<u64>,
    },
    StrLit {
        ptr: StringPtr<'a>,
        key: Cell<u64>,
    },
    Thunk {
        env: E<'a>,
        expr: ExprPtr<'a>,
        forced: OnceCell<V<'a>>,
        key: Cell<u64>,
    },
}

#[inline]
pub fn kmix(a: u64, b: u64) -> u64 { (a ^ b).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(29) }

const KEY_PRESENT: u64 = 1 << 63;

#[inline]
fn seal(d: u64, closed: bool) -> u64 { (d & !1) | u64::from(closed) | KEY_PRESENT }

impl<'a> Value<'a> {
    #[inline]
    fn key_cell(&self) -> &Cell<u64> {
        match self {
            Value::Rigid { key, .. }
            | Value::Unfold { key, .. }
            | Value::Lam { key, .. }
            | Value::Pi { key, .. }
            | Value::Sort { key, .. }
            | Value::NatLit { key, .. }
            | Value::StrLit { key, .. }
            | Value::Thunk { key, .. } => key,
        }
    }

    #[inline]
    pub fn digest(&self) -> u64 {
        let cell = self.key_cell();
        let k = cell.get();
        if k & KEY_PRESENT != 0 {
            return k;
        }
        let d = self.compute_key();
        cell.set(d);
        d
    }

    #[inline]
    pub fn is_canonical(&self) -> bool {
        match self {
            Value::Rigid { canon, .. }
            | Value::Unfold { canon, .. }
            | Value::Lam { canon, .. }
            | Value::Pi { canon, .. } => canon.get(),
            _ => false,
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

    fn compute_key(&self) -> u64 {
        match self {
            Value::Rigid { head, spine, .. } => {
                let (h, c) = head_key(*head);
                seal(kmix(h, spine.key()), c && spine.is_closed())
            }
            Value::Unfold { head, spine, .. } => {
                let h = kmix(kmix(10, head.name.get_hash()), head.levels.get_hash());
                seal(kmix(h, spine.key()), spine.is_closed())
            }
            Value::Lam { binder_name, binder_style, binder_type, body, .. } => {
                let (b, c) = closure_key(body);
                let h = kmix(
                    kmix(kmix(11, binder_name.get_hash()), *binder_style as u64),
                    binder_type.as_ref() as *const crate::expr::Expr<'a> as usize as u64,
                );
                seal(kmix(h, b), c)
            }
            Value::Pi { binder_name, binder_style, domain, body, .. } => {
                let (b, c) = closure_key(body);
                let h = kmix(kmix(12, binder_name.get_hash()), *binder_style as u64);
                seal(kmix(kmix(h, domain.digest()), b), c && domain.is_closed())
            }
            Value::Sort { level, .. } => seal(kmix(1, level.get_hash()), true),
            Value::NatLit { ptr, .. } => seal(kmix(2, ptr.get_hash()), true),
            Value::StrLit { ptr, .. } => seal(kmix(3, ptr.get_hash()), true),
            Value::Thunk { env, expr, .. } => {
                let (e, c) = env_slots_key(env, expr.num_loose_bvars());
                seal(kmix(kmix(13, expr.as_ref() as *const crate::expr::Expr<'a> as usize as u64), e), c)
            }
        }
    }

    #[inline]
    pub fn is_closed(&self) -> bool { self.digest() & 1 == 1 }
}

fn head_key(head: RigidHead<'_>) -> (u64, bool) {
    match head {
        RigidHead::BVar(lvl, ty) => (kmix(kmix(4, u64::from(lvl)), ty.digest()), false),
        RigidHead::Axiom(n, ls) => (kmix(kmix(5, n.get_hash()), ls.get_hash()), true),
        RigidHead::Ctor(n, ls) => (kmix(kmix(6, n.get_hash()), ls.get_hash()), true),
        RigidHead::Recursor(n, ls) => (kmix(kmix(7, n.get_hash()), ls.get_hash()), true),
        RigidHead::QuotConst(n, ls) => (kmix(kmix(8, n.get_hash()), ls.get_hash()), true),
        RigidHead::Inductive(n, ls) => (kmix(kmix(9, n.get_hash()), ls.get_hash()), true),
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
    let d = kmix(clo.body.as_ref() as *const crate::expr::Expr<'_> as usize as u64, e);
    (d, c && clo.ctx.is_none())
}

#[derive(Debug)]
pub struct LevelSub<'a> {
    pub ks: LevelsPtr<'a>,
    pub vs: LevelsPtr<'a>,
}

#[derive(Debug)]
pub enum Env<'a> {
    Nil { lsub: Option<&'a LevelSub<'a>>, hash: u64 },
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
}

pub fn lsub_key(lsub: Option<&LevelSub<'_>>) -> u64 {
    match lsub {
        None => 1,
        Some(ls) => kmix(kmix(14, ls.ks.get_hash()), ls.vs.get_hash()) | 1,
    }
}

impl<'a> Env<'a> {
    #[inline]
    pub fn get_hash(&self) -> u64 {
        match self {
            Env::Nil { hash, .. } | Env::Cons { hash, .. } | Env::Framed { hash, .. } => *hash,
        }
    }

    #[inline]
    pub fn len(&self) -> u32 {
        match self {
            Env::Nil { .. } => 0,
            Env::Cons { len, .. } | Env::Framed { len, .. } => *len,
        }
    }

    #[inline]
    pub fn lsub(&self) -> Option<&'a LevelSub<'a>> {
        match self {
            Env::Nil { lsub, .. } | Env::Cons { lsub, .. } | Env::Framed { lsub, .. } => *lsub,
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
    Snoc { prev: S<'a>, elim: Elim<'a>, len: u32, canon: Cell<bool>, has_proj: bool, key: Cell<u64> },
}

impl<'a> Spine<'a> {
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
        let Spine::Snoc { prev, elim, key, .. } = self else { return seal(15, true) };
        let k = key.get();
        if k & KEY_PRESENT != 0 {
            return k;
        }
        let k = match elim.view() {
            ElimView::App(v) => seal(kmix(prev.key(), v.digest()), prev.is_closed() && v.is_closed()),
            ElimView::Proj { ty_name, idx } => seal(
                kmix(kmix(prev.key(), ty_name.get_hash()), u64::from(idx) | (1 << 60)),
                prev.is_closed(),
            ),
        };
        key.set(k);
        k
    }

    #[inline]
    pub fn is_closed(&self) -> bool { self.key() & 1 == 1 }
}

impl<'a> Env<'a> {
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
            }
        }
    }
}

impl<'a> Closure<'a> {
    pub fn mk_eval(env: E<'a>, body: ExprPtr<'a>) -> Self { Closure { env, ctx: None, body } }

    pub fn mk_infer(env: E<'a>, ctx: C<'a>, body: ExprPtr<'a>) -> Self { Closure { env, ctx: Some(ctx), body } }
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

    pub fn is_empty(&self) -> bool { matches!(self, Spine::Empty) }

    #[inline]
    pub fn len(&self) -> u32 {
        match self {
            Spine::Empty => 0,
            Spine::Snoc { len, .. } => *len,
        }
    }
    pub fn to_vec<'b>(&'b self) -> Vec<&'b Elim<'a>> {
        let len = self.len() as usize;
        let mut out = Vec::with_capacity(len);
        let mut cur: &Spine<'a> = self;
        while let Spine::Snoc { prev, elim, .. } = cur {
            out.push(elim);
            cur = prev;
        }
        out.reverse();
        out
    }
    pub fn get(&self, i: usize) -> Option<&Elim<'a>> {
        let len = self.len() as usize;
        let mut steps = len.checked_sub(i + 1)?;
        let mut cur = self;
        while let Spine::Snoc { prev, elim, .. } = cur {
            if steps == 0 {
                return Some(elim);
            }
            steps -= 1;
            cur = prev;
        }
        None
    }
}

pub fn env_empty<'a>(arena: &'a Bump) -> E<'a> {
    arena.alloc(Env::Nil { lsub: None, hash: 0 })
}
pub fn env_extend<'a>(arena: &'a Bump, parent: E<'a>, v: V<'a>) -> E<'a> {
    let v_hash = v as *const Value<'a> as usize as u64;
    let parent_hash = parent.get_hash();
    let hash = parent_hash.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(v_hash);
    arena.alloc(Env::Cons {
        v,
        parent,
        lsub: parent.lsub(),
        hash,
        len: parent.len() + 1,
        prune: Cell::new((0, None)),
    })
}
pub fn ctx_empty<'a>(arena: &'a Bump) -> C<'a> { arena.alloc(Ctx::Nil) }
pub fn ctx_extend<'a>(arena: &'a Bump, parent: C<'a>, ty: V<'a>) -> C<'a> { arena.alloc(Ctx::Cons { ty, parent }) }
pub fn spine_empty<'a>(arena: &'a Bump) -> S<'a> { arena.alloc(Spine::Empty) }
pub fn spine_snoc<'a>(arena: &'a Bump, prev: S<'a>, elim: Elim<'a>) -> S<'a> {
    arena.alloc(Spine::Snoc {
        prev,
        elim,
        len: prev.len() + 1,
        canon: Cell::new(false),
        has_proj: prev.has_proj() || !elim.is_app(),
        key: Cell::new(0),
    })
}

pub fn mk_rigid<'a>(arena: &'a Bump, head: RigidHead<'a>, spine: S<'a>) -> V<'a> {
    arena.alloc(Value::Rigid { head, spine, canon: Cell::new(false), key: Cell::new(0) })
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
        key: Cell::new(0),
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
    arena.alloc(Value::Unfold { head: UnfoldHead { name, levels }, spine: empty, head_value, forced, canon: Cell::new(false), key: Cell::new(0) })
}
pub fn mk_lam<'a>(
    arena: &'a Bump,
    binder_name: NamePtr<'a>,
    binder_style: BinderStyle,
    binder_type: ExprPtr<'a>,
    body: Closure<'a>,
) -> V<'a> {
    arena.alloc(Value::Lam { binder_name, binder_style, binder_type, body, canon: Cell::new(false), key: Cell::new(0) })
}
pub fn mk_pi<'a>(
    arena: &'a Bump,
    binder_name: NamePtr<'a>,
    binder_style: BinderStyle,
    domain: V<'a>,
    body: Closure<'a>,
) -> V<'a> {
    arena.alloc(Value::Pi { binder_name, binder_style, domain, body, canon: Cell::new(false), key: Cell::new(0) })
}
pub fn mk_sort<'a>(arena: &'a Bump, level: LevelPtr<'a>) -> V<'a> {
    arena.alloc(Value::Sort { level, key: Cell::new(0) })
}
pub fn mk_natlit<'a>(arena: &'a Bump, ptr: BigUintPtr<'a>) -> V<'a> {
    arena.alloc(Value::NatLit { ptr, key: Cell::new(0) })
}
pub fn mk_strlit<'a>(arena: &'a Bump, ptr: StringPtr<'a>) -> V<'a> {
    arena.alloc(Value::StrLit { ptr, key: Cell::new(0) })
}
pub fn mk_bvar_with_empty<'a>(arena: &'a Bump, level: u32, ty: V<'a>, empty: S<'a>) -> V<'a> {
    mk_rigid(arena, RigidHead::BVar(level, ty), empty)
}
pub fn mk_rigid_head_with_empty<'a>(arena: &'a Bump, head: RigidHead<'a>, empty: S<'a>) -> V<'a> {
    mk_rigid(arena, head, empty)
}
pub fn mk_thunk<'a>(arena: &'a Bump, env: E<'a>, expr: ExprPtr<'a>) -> V<'a> {
    arena.alloc(Value::Thunk { env, expr, forced: OnceCell::new(), key: Cell::new(0) })
}

const _: () = assert!(std::mem::size_of::<Value<'static>>() == 56);
const _: () = assert!(std::mem::size_of::<Spine<'static>>() == 32);

pub fn forced_of<'a>(v: V<'a>) -> Option<V<'a>> {
    match v {
        Value::Thunk { forced, .. } | Value::Unfold { forced, .. } => forced.get().copied(),
        _ => None,
    }
}
