use crate::checker::env::{Declar, DeclarInfo};
use crate::term::expr::Expr;
use crate::term::hash::FxHashMap;
use crate::term::id::{BigId, ExprId, LevelId, LevelsId, NameId, StrId};
use crate::term::intern::Terms;
use crate::term::level::Level;
use crate::term::name::Name;

pub(crate) struct Promoter<'a> {
    source: Terms,
    target: &'a mut Terms,
    names: FxHashMap<NameId, NameId>,
    levels: FxHashMap<LevelId, LevelId>,
    lists: FxHashMap<LevelsId, LevelsId>,
    exprs: FxHashMap<ExprId, ExprId>,
}

impl<'a> Promoter<'a> {
    pub(crate) fn new(source: Terms, target: &'a mut Terms) -> Self {
        Self {
            source,
            target,
            names: FxHashMap::default(),
            levels: FxHashMap::default(),
            lists: FxHashMap::default(),
            exprs: FxHashMap::default(),
        }
    }

    fn string(&mut self, s: StrId) -> StrId {
        if !s.is_local() {
            return s;
        }
        StrId::new(
            self.target
                .strings
                .intern_ref(self.source.strings.items[s.index()].as_ref()),
            false,
        )
    }

    fn big(&mut self, b: BigId) -> BigId {
        if !b.is_local() {
            return b;
        }
        BigId::new(
            self.target
                .bignums
                .intern(self.source.bignums.items[b.index()].clone()),
            false,
        )
    }

    fn name(&mut self, n: NameId) -> NameId {
        if !n.is_local() {
            return n;
        }
        if let Some(&name) = self.names.get(&n) {
            return name;
        }
        let name = match self.source.names.items[n.index()] {
            Name::Anon => Name::Anon,
            Name::Str(p, s) => Name::Str(self.name(p), self.string(s)),
            Name::Num(p, i) => Name::Num(self.name(p), i),
        };
        let result = NameId::new(self.target.names.intern(name), false);
        self.names.insert(n, result);
        result
    }

    fn level(&mut self, l: LevelId) -> LevelId {
        if !l.is_local() {
            return l;
        }
        if let Some(&level) = self.levels.get(&l) {
            return level;
        }
        let level = match self.source.levels.items[l.index()] {
            Level::Zero => Level::Zero,
            Level::Param(n) => Level::Param(self.name(n)),
            Level::Succ(l) => Level::Succ(self.level(l)),
            Level::Max(l, r) => Level::Max(self.level(l), self.level(r)),
            Level::IMax(l, r) => Level::IMax(self.level(l), self.level(r)),
        };
        let result = LevelId::new(self.target.levels.intern(level), false);
        self.levels.insert(l, result);
        result
    }

    fn levels(&mut self, ls: LevelsId) -> LevelsId {
        if !ls.is_local() {
            return ls;
        }
        if let Some(&levels) = self.lists.get(&ls) {
            return levels;
        }
        let source = self.source.lists.items[ls.index()].to_vec();
        let levels: Vec<_> = source.into_iter().map(|l| self.level(l)).collect();
        let result = LevelsId::new(self.target.lists.intern_ref(levels.as_slice()), false);
        self.lists.insert(ls, result);
        result
    }

    fn expr(&mut self, e: ExprId) -> ExprId {
        if !e.is_local() {
            return e;
        }
        if let Some(&expr) = self.exprs.get(&e) {
            return expr;
        }
        let mut node = self.source.exprs.items[e.index()];
        node.expr = node.expr.map_children(|e, _| self.expr(e));
        node.expr = match node.expr {
            Expr::Sort { level } => Expr::Sort {
                level: self.level(level),
            },
            Expr::Const { name, levels } => Expr::Const {
                name: self.name(name),
                levels: self.levels(levels),
            },
            Expr::Proj {
                ty_name,
                idx,
                structure,
            } => Expr::Proj {
                ty_name: self.name(ty_name),
                idx,
                structure,
            },
            Expr::NatLit { lit } => Expr::NatLit { lit: self.big(lit) },
            Expr::StringLit { lit } => Expr::StringLit {
                lit: self.string(lit),
            },
            expr => expr,
        };
        let result = ExprId::new(self.target.exprs.intern(node), false);
        self.exprs.insert(e, result);
        result
    }

    fn info(&mut self, info: DeclarInfo) -> DeclarInfo {
        DeclarInfo {
            name: self.name(info.name),
            ty: self.expr(info.ty),
            uparams: self.levels(info.uparams),
        }
    }

    pub(crate) fn declar(&mut self, mut declar: Declar) -> Declar {
        match &mut declar {
            Declar::Quot { info } => *info = self.info(*info),
            Declar::Inductive(ind) => {
                ind.info = self.info(ind.info);
                ind.all_ind_names = ind.all_ind_names.iter().map(|&n| self.name(n)).collect();
                ind.all_ctor_names = ind.all_ctor_names.iter().map(|&n| self.name(n)).collect();
            }
            Declar::Constructor(ctor) => {
                ctor.info = self.info(ctor.info);
                ctor.inductive_name = self.name(ctor.inductive_name);
            }
            Declar::Recursor(rec) => {
                rec.info = self.info(rec.info);
                rec.all_inductives = rec.all_inductives.iter().map(|&n| self.name(n)).collect();
                rec.rec_rules = rec
                    .rec_rules
                    .iter()
                    .map(|rule| {
                        let mut rule = *rule;
                        rule.ctor_name = self.name(rule.ctor_name);
                        rule.val = self.expr(rule.val);
                        rule
                    })
                    .collect();
            }
            _ => unreachable!(),
        }
        declar
    }
}
