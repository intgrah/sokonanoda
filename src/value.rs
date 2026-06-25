use crate::expr::BinderStyle;
use crate::util::{BigUintPtr, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};
use bumpalo::Bump;
use std::cell::OnceCell;

pub type V<'a> = &'a Value<'a>;
pub type E<'a> = &'a Env<'a>;
pub type C<'a> = &'a Ctx<'a>;
pub type S<'a> = &'a Spine<'a>;

#[derive(Debug)]
pub struct Closure<'a> {
    pub env: E<'a>,
    pub body: ExprPtr<'a>,
}

#[derive(Debug, Clone, Copy)]
pub enum RigidHead<'a> {
    BVar(u32, V<'a>),
    Local(ExprPtr<'a>),
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

#[derive(Debug)]
pub enum Elim<'a> {
    App(V<'a>),
    Proj { ty_name: NamePtr<'a>, idx: usize },
}

#[derive(Debug)]
pub enum Value<'a> {
    Rigid {
        head: RigidHead<'a>,
        spine: S<'a>,
    },
    Unfold {
        head: UnfoldHead<'a>,
        spine: S<'a>,
        head_value: &'a OnceCell<V<'a>>,
        forced: OnceCell<V<'a>>,
    },
    Lam {
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        domain: OnceCell<V<'a>>,
        body: Closure<'a>,
    },
    Pi {
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        domain: V<'a>,
        body: Closure<'a>,
    },
    Sort {
        level: LevelPtr<'a>,
    },
    NatLit {
        ptr: BigUintPtr<'a>,
    },
    StrLit {
        ptr: StringPtr<'a>,
    },
    Thunk {
        env: E<'a>,
        expr: ExprPtr<'a>,
        forced: OnceCell<V<'a>>,
    },
}

#[derive(Debug)]
pub enum Env<'a> {
    Nil,
    Cons { v: V<'a>, parent: E<'a>, hash: u64 },
}

impl<'a> Env<'a> {
    #[inline]
    pub fn get_hash(&self) -> u64 {
        match self {
            Env::Nil => 0,
            Env::Cons { hash, .. } => *hash,
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
    Snoc(S<'a>, Elim<'a>),
}

impl<'a> Env<'a> {
    pub fn lookup(&self, mut idx: u16) -> Option<V<'a>> {
        let mut cur = self;
        while let Env::Cons { v, parent, .. } = cur {
            if idx == 0 {
                return Some(*v);
            }
            idx -= 1;
            cur = parent;
        }
        None
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
    pub fn is_empty(&self) -> bool { matches!(self, Spine::Empty) }

    pub fn len(&self) -> u32 {
        let mut n = 0u32;
        let mut cur = self;
        while let Spine::Snoc(prev, _) = cur {
            n += 1;
            cur = prev;
        }
        n
    }
    pub fn to_vec<'b>(&'b self) -> Vec<&'b Elim<'a>> {
        let len = self.len() as usize;
        let mut out = Vec::with_capacity(len);
        let mut cur: &Spine<'a> = self;
        while let Spine::Snoc(prev, elim) = cur {
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
        while let Spine::Snoc(prev, elim) = cur {
            if steps == 0 {
                return Some(elim);
            }
            steps -= 1;
            cur = prev;
        }
        None
    }
}

pub fn env_empty<'a>(arena: &'a Bump) -> E<'a> { arena.alloc(Env::Nil) }
pub fn env_extend<'a>(arena: &'a Bump, parent: E<'a>, v: V<'a>) -> E<'a> {
    let v_hash = v as *const Value<'a> as usize as u64;
    let parent_hash = parent.get_hash();
    let hash = parent_hash.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(v_hash);
    arena.alloc(Env::Cons { v, parent, hash })
}
pub fn ctx_empty<'a>(arena: &'a Bump) -> C<'a> { arena.alloc(Ctx::Nil) }
pub fn ctx_extend<'a>(arena: &'a Bump, parent: C<'a>, ty: V<'a>) -> C<'a> { arena.alloc(Ctx::Cons { ty, parent }) }
pub fn spine_empty<'a>(arena: &'a Bump) -> S<'a> { arena.alloc(Spine::Empty) }
pub fn spine_snoc<'a>(arena: &'a Bump, prev: S<'a>, elim: Elim<'a>) -> S<'a> { arena.alloc(Spine::Snoc(prev, elim)) }

pub fn mk_rigid<'a>(arena: &'a Bump, head: RigidHead<'a>, spine: S<'a>) -> V<'a> {
    arena.alloc(Value::Rigid { head, spine })
}

pub fn mk_unfold<'a>(
    arena: &'a Bump,
    name: NamePtr<'a>,
    levels: LevelsPtr<'a>,
    spine: S<'a>,
    head_value: &'a OnceCell<V<'a>>,
) -> V<'a> {
    arena.alloc(Value::Unfold { head: UnfoldHead { name, levels }, spine, head_value, forced: OnceCell::new() })
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
    arena.alloc(Value::Unfold { head: UnfoldHead { name, levels }, spine: empty, head_value, forced })
}
pub fn mk_lam<'a>(
    arena: &'a Bump,
    binder_name: NamePtr<'a>,
    binder_style: BinderStyle,
    binder_type: ExprPtr<'a>,
    body: Closure<'a>,
) -> V<'a> {
    arena.alloc(Value::Lam { binder_name, binder_style, binder_type, domain: OnceCell::new(), body })
}
pub fn mk_pi<'a>(
    arena: &'a Bump,
    binder_name: NamePtr<'a>,
    binder_style: BinderStyle,
    domain: V<'a>,
    body: Closure<'a>,
) -> V<'a> {
    arena.alloc(Value::Pi { binder_name, binder_style, domain, body })
}
pub fn mk_sort<'a>(arena: &'a Bump, level: LevelPtr<'a>) -> V<'a> { arena.alloc(Value::Sort { level }) }
pub fn mk_natlit<'a>(arena: &'a Bump, ptr: BigUintPtr<'a>) -> V<'a> { arena.alloc(Value::NatLit { ptr }) }
pub fn mk_strlit<'a>(arena: &'a Bump, ptr: StringPtr<'a>) -> V<'a> { arena.alloc(Value::StrLit { ptr }) }
pub fn mk_local_with_empty<'a>(arena: &'a Bump, e: ExprPtr<'a>, empty: S<'a>) -> V<'a> {
    arena.alloc(Value::Rigid { head: RigidHead::Local(e), spine: empty })
}
pub fn mk_bvar_with_empty<'a>(arena: &'a Bump, level: u32, ty: V<'a>, empty: S<'a>) -> V<'a> {
    arena.alloc(Value::Rigid { head: RigidHead::BVar(level, ty), spine: empty })
}
pub fn mk_rigid_head_with_empty<'a>(arena: &'a Bump, head: RigidHead<'a>, empty: S<'a>) -> V<'a> {
    arena.alloc(Value::Rigid { head, spine: empty })
}
pub fn mk_thunk<'a>(arena: &'a Bump, env: E<'a>, expr: ExprPtr<'a>) -> V<'a> {
    arena.alloc(Value::Thunk { env, expr, forced: OnceCell::new() })
}
