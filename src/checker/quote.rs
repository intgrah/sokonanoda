use crate::checker::cache::memo;
use crate::checker::tc::TypeChecker;
use crate::checker::value::{ElimView, RigidHead, S, Spine, V, Value};
use crate::term::ptr::{ExprPtr, Id};

impl<'t> TypeChecker<'_, 't, '_> {
    pub(crate) fn quote(&mut self, depth: u32, v: V<'t>) -> ExprPtr<'t> {
        memo!(
            self.tc_cache.quote_cache,
            (Id::of(v), depth),
            match v {
                Value::Sort { level, .. } => self.ctx.mk_sort(*level),
                Value::NatLit { ptr, .. } => self
                    .ctx
                    .mk_nat_lit(*ptr)
                    .expect("quote: nat literal without extension"),
                Value::StrLit { ptr, .. } => self
                    .ctx
                    .mk_string_lit(*ptr)
                    .expect("quote: string literal without extension"),
                Value::Rigid { head, spine, .. } => {
                    let head = self.quote_rigid_head(depth, *head);
                    self.quote_spine(depth, head, spine)
                }
                Value::Unfold { head, spine, .. } => {
                    let h = self.ctx.mk_const(head.name, head.levels);
                    self.quote_spine(depth, h, spine)
                }
                Value::Lam { body, .. } => {
                    let dom = self.lam_domain(depth, v);
                    let fresh = self.mk_bvar_hc(depth, dom);
                    let body = self.apply_closure(depth + 1, body, fresh, None);
                    let dom_e = self.quote(depth, dom);
                    let body_e = self.quote(depth + 1, body);
                    self.ctx.mk_lambda(dom_e, body_e)
                }
                Value::Pi { domain, body, .. } => {
                    let domain = *domain;
                    let fresh = self.mk_bvar_hc(depth, domain);
                    let body = self.apply_closure(depth + 1, body, fresh, Some(domain));
                    let dom_e = self.quote(depth, domain);
                    let body_e = self.quote(depth + 1, body);
                    self.ctx.mk_pi(dom_e, body_e)
                }
            }
        )
    }

    fn quote_rigid_head(&mut self, depth: u32, head: RigidHead<'t>) -> ExprPtr<'t> {
        match head {
            RigidHead::BVar(lvl, _) => {
                assert!(lvl < depth, "quote: bound variable escaped its binder");
                let idx = u16::try_from(depth - 1 - lvl).expect("quote: binder depth exceeds u16");
                self.ctx.mk_var(idx)
            }
            RigidHead::Axiom(n, ls)
            | RigidHead::Ctor(n, ls)
            | RigidHead::Recursor(n, ls)
            | RigidHead::QuotConst(n, ls)
            | RigidHead::Inductive(n, ls) => self.ctx.mk_const(n, ls),
        }
    }

    fn quote_spine(&mut self, depth: u32, head: ExprPtr<'t>, s: S<'t>) -> ExprPtr<'t> {
        match s {
            Spine::Empty => head,
            Spine::Snoc { prev, elim, .. } => {
                let prefix = self.quote_spine(depth, head, prev);
                match elim.view() {
                    ElimView::App(a) => {
                        let a = self.quote(depth, a);
                        self.ctx.mk_app(prefix, a)
                    }
                    ElimView::Proj { ty_name, idx } => self.ctx.mk_proj(ty_name, idx, prefix),
                }
            }
        }
    }

    pub(crate) fn quote_weak(&mut self, depth: u32, v: V<'t>) -> ExprPtr<'t> {
        match v {
            Value::Rigid { head, spine, .. } => {
                let head = self.quote_rigid_head(depth, *head);
                self.quote_spine_weak(depth, head, spine)
            }
            Value::Unfold { head, spine, .. } => {
                let h = self.ctx.mk_const(head.name, head.levels);
                self.quote_spine_weak(depth, h, spine)
            }
            _ => self.quote(depth, v),
        }
    }

    fn quote_spine_weak(&mut self, depth: u32, head: ExprPtr<'t>, s: S<'t>) -> ExprPtr<'t> {
        match s {
            Spine::Empty => head,
            Spine::Snoc { prev, elim, .. } => {
                let prefix = self.quote_spine_weak(depth, head, prev);
                match elim.view() {
                    ElimView::App(a) => {
                        let a = self.quote_weak(depth, a);
                        self.ctx.mk_app(prefix, a)
                    }
                    ElimView::Proj { ty_name, idx } => self.ctx.mk_proj(ty_name, idx, prefix),
                }
            }
        }
    }

    pub(crate) fn force_pi(&mut self, depth: u32, cur: V<'t>) -> Option<V<'t>> {
        let f = self.force_all(depth, cur);
        matches!(f, Value::Pi { .. }).then_some(f)
    }

    pub(crate) fn value_of(&mut self, e: ExprPtr<'t>) -> V<'t> {
        let depth = 0u32;
        let env = self.empty_env();
        self.eval(depth, env, e)
    }
}
