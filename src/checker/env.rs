// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::context::TcCtx;
use crate::term::expr::Expr;
use crate::term::hash::FxIndexMap;
use crate::term::id::{ExprId, LevelsId, NameId};
use serde::Deserialize;
use std::collections::HashSet;
use std::sync::Arc;

/// Reducibility hints accompany definitions; used to determine how
/// to unfold expressions in order to most efficiently proceed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Deserialize)]
pub enum ReducibilityHint {
    #[serde(rename = "opaque")]
    Opaque,
    #[serde(rename = "regular")]
    Regular(u16),
    #[serde(rename = "abbrev")]
    Abbrev,
}

impl ReducibilityHint {
    /// Check whether `self` is "less than" `other` in terms of reducibility; during
    /// delta reduction in equality checking, we want to unfold the greater of the two
    /// definitions to try and bring the two closer.
    pub(crate) fn is_lt(self, other: Self) -> bool {
        use ReducibilityHint::{Abbrev, Opaque, Regular};
        match (self, other) {
            (_, Opaque) | (Abbrev, _) => false,
            (Opaque, _) | (_, Abbrev) => true,
            (Regular(h1), Regular(h2)) => h1 < h2,
        }
    }
}

/// Convenience declaration for the elements common across all kinds
/// of declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclarInfo {
    pub name: NameId,
    pub uparams: LevelsId,
    pub ty: ExprId,
}

/// Computation rules for iota-reduction (pattern matching).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecRule {
    pub ctor_name: NameId,
    /// the constructor's telescope size minus the params (but including indices).
    /// So a constructor with 2 params, 1 index, and 4 args is (1 + 4) = 5.
    pub ctor_telescope_size_wo_params: u16,
    pub val: ExprId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Declar {
    Axiom {
        info: DeclarInfo,
    },
    Quot {
        info: DeclarInfo,
    },
    Theorem {
        info: DeclarInfo,
        val: ExprId,
    },
    Definition {
        info: DeclarInfo,
        val: ExprId,
        hint: ReducibilityHint,
    },
    Opaque {
        info: DeclarInfo,
        val: ExprId,
    },
    Inductive(InductiveData),
    Constructor(ConstructorData),
    Recursor(RecursorData),
}

/// This structure is what's taken from the export file; it contains enough
/// information to begin the process of checking an inductive declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveData {
    pub(crate) info: DeclarInfo,
    /// `true` when recursive (that is, the inductive type appears as an argument in a constructor).
    pub(crate) is_recursive: bool,
    /// `true` when this typs is a nested inductive
    pub(crate) is_nested: bool,
    /// All inductive types in a mutual block must have the same parameters, though this
    /// does not exactly hold for nested inductives.
    pub(crate) num_params: u16,
    pub(crate) num_indices: u16,
    /// The names of this type, and any other inductive types in a `mutual..end`
    /// block. No nested inductive info is conveyed here.
    pub(crate) all_ind_names: Arc<[NameId]>,
    /// The constructor names for THIS type only. No constructors
    /// from other elements in a mutual block, nothing from any nested
    /// construction.
    pub(crate) all_ctor_names: Arc<[NameId]>,
}

impl InductiveData {
    pub fn aux_data_ck(&self, other: &Self) -> bool {
        self.info.name == other.info.name
            && self.num_params == other.num_params
            && self.num_indices == other.num_indices
            && self.is_nested == other.is_nested
            && self.all_ctor_names.iter().collect::<HashSet<_>>()
                == other.all_ctor_names.iter().collect::<HashSet<_>>()
            && if other.is_nested {
                self.all_ind_names
                    .iter()
                    .collect::<HashSet<_>>()
                    .is_subset(&other.all_ind_names.iter().collect::<HashSet<_>>())
            } else {
                self.all_ind_names.iter().collect::<HashSet<_>>()
                    == other.all_ind_names.iter().collect::<HashSet<_>>()
            }
    }
}

/// `inductive_name` is the name of the type this constructs. e.g. `Prod` for `Prod.mk`
///
/// `ctor_idx` is 0-based; e.g. `List.nil (ctor_idx := 0)`, `List.cons (ctor_idx := 1)`
///
/// `num_params` is the number of parameters in the inductive specification, not including ctor args;
/// `num_fields` is the number of ctor args, not including parameters.
///
/// `Prod.mk (A B) (a b) ;;
/// (num_params := 2) (num_fields := 2)`
///
/// `HAppend.mk {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) → HAppend α β γ
/// (num_params := 3) (num_fields := 1)`
///
/// `Syntax.node (num_params := 0) (num_fields := 3)`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorData {
    pub info: DeclarInfo,
    pub inductive_name: NameId,
    pub ctor_idx: u16,
    /// The number of parameters, not including ctor args
    pub num_params: u16,
    /// The number of ctor args, not including parameters.
    pub num_fields: u16,
}

impl ConstructorData {
    pub fn aux_data_ck(&self, other: &Self) -> bool {
        self.info.name == other.info.name
            && self.inductive_name == other.inductive_name
            && self.ctor_idx == other.ctor_idx
            && self.num_params == other.num_params
            && self.num_fields == other.num_fields
    }
}

/// Information received from the export file regarding a recursor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorData {
    pub info: DeclarInfo,
    pub all_inductives: Arc<[NameId]>,
    pub num_params: u16,
    pub num_indices: u16,
    pub num_motives: u16,
    pub num_minors: u16,
    pub rec_rules: Arc<[RecRule]>,
    pub is_k: bool,
}

impl RecursorData {
    /// Compute the index in the recursor's type (in the telescope) where the major premise is located.
    pub fn major_idx(&self) -> usize {
        (self.num_params + self.num_motives + self.num_minors + self.num_indices) as usize
    }

    pub fn aux_data_ck(&self, other: &Self) -> bool {
        self.info.name == other.info.name
            && self.num_params == other.num_params
            && self.num_indices == other.num_indices
            && self.num_motives == other.num_motives
            && self.num_minors == other.num_minors
            && self.is_k == other.is_k
            && self.all_inductives.iter().collect::<HashSet<_>>()
                == other.all_inductives.iter().collect::<HashSet<_>>()
    }
}

impl Declar {
    pub(crate) fn kind(&self) -> &'static str {
        match self {
            Declar::Axiom { .. } => "axiom",
            Declar::Quot { .. } => "quot",
            Declar::Theorem { .. } => "theorem",
            Declar::Definition { .. } => "def",
            Declar::Opaque { .. } => "opaque",
            Declar::Inductive(..) => "inductive",
            Declar::Constructor(..) => "ctor",
            Declar::Recursor(..) => "recr",
        }
    }

    pub fn info(&self) -> &DeclarInfo {
        use Declar::{Axiom, Constructor, Definition, Inductive, Opaque, Quot, Recursor, Theorem};
        match self {
            Axiom { info, .. }
            | Quot { info, .. }
            | Theorem { info, .. }
            | Definition { info, .. }
            | Inductive(InductiveData { info, .. })
            | Constructor(ConstructorData { info, .. })
            | Recursor(RecursorData { info, .. })
            | Opaque { info, .. } => info,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum EnvLimit {
    ByIndex(usize),
    ByName(NameId),
}

/// A Lean environment, which consists of a set of declarations that my have a temporary
/// extension. The temporary extensions are used to acommodate
/// the specialization process needed for checking nested inductives.
///
/// When a tyep checker looks up a declaration in the environment, it will check the temporary
/// extension first if there is one, then fall back to the persistent map.
pub struct Env<'x> {
    declars: &'x DeclarMap,
    decl_of: &'x [u32],
    /// Used for checking nested inductives.
    temp_declars: Option<&'x DeclarMap>,
    /// `cutoff` is used to mark the end of what should be the "visible" environment.
    /// This allows us to make the complete environment at parse time, and then control visibility
    /// between threads by only making a particular slice of that environment available to a thread.
    cutoff: usize,
}

pub(crate) type DeclarMap = FxIndexMap<NameId, Declar>;

impl<'x> Env<'x> {
    /// Create a new environment (without any temporary extension)
    pub fn new(declars: &'x DeclarMap, decl_of: &'x [u32], limit: EnvLimit) -> Self {
        Self::new_w_temp_ext(declars, decl_of, None, limit)
    }

    /// Create a new environment that includes some temporary extension; the temporary
    /// extension is used for checking nested inductives.
    pub fn new_w_temp_ext(
        declars: &'x DeclarMap,
        decl_of: &'x [u32],
        temp_declars: Option<&'x DeclarMap>,
        limit: EnvLimit,
    ) -> Self {
        let cutoff = match limit {
            EnvLimit::ByIndex(idx) => idx,
            EnvLimit::ByName(n) => match Self::lookup_idx(decl_of, n) {
                crate::term::name::NO_DECL => 0,
                idx => idx as usize,
            },
        };
        Self {
            declars,
            decl_of,
            temp_declars,
            cutoff,
        }
    }

    #[inline]
    fn lookup_idx(decl_of: &[u32], n: NameId) -> u32 {
        if n.is_local() {
            return crate::term::name::NO_DECL;
        }
        decl_of
            .get(n.index())
            .copied()
            .unwrap_or(crate::term::name::NO_DECL)
    }

    /// Retrieve a declaration by first checking the contents of any temporary extension,
    /// then checking the persistent environment.
    pub fn get_declar(&self, n: NameId) -> Option<&Declar> {
        self.temp_declars
            .as_ref()
            .and_then(|ext| ext.get(&n))
            .or_else(|| self.get_old_declar(n))
    }

    pub fn has_temp_ext(&self) -> bool {
        self.temp_declars.is_some()
    }

    /// Get a declaration, only looking in the temporary extension.
    pub fn get_temp_declar(&self, n: NameId) -> Option<&Declar> {
        self.temp_declars.as_ref().and_then(|ext| ext.get(&n))
    }

    /// Get a declaration, bypassing the temporary extension, only searching in
    /// the persistent set of declarations.
    pub fn get_old_declar(&self, n: NameId) -> Option<&Declar> {
        let idx = Self::lookup_idx(self.decl_of, n) as usize;
        if idx < self.cutoff {
            Some(&self.declars[idx])
        } else {
            None
        }
    }

    pub fn get_inductive(&self, n: NameId) -> Option<&InductiveData> {
        match self.get_declar(n) {
            Some(Declar::Inductive(i)) => Some(i),
            _ => None,
        }
    }

    pub fn get_recursor(&self, n: NameId) -> Option<&RecursorData> {
        match self.get_declar(n) {
            Some(Declar::Recursor(r)) => Some(r),
            _ => None,
        }
    }

    #[inline]
    pub fn get_constructor(&self, n: NameId) -> Option<&ConstructorData> {
        match self.get_declar(n) {
            Some(Declar::Constructor(c)) => Some(c),
            _ => None,
        }
    }

    /// Returns `true` iff the inductive type declaration associated with `n` has the
    /// characteristics required of a structure. The requirements to be a structure are
    /// (1) the inductive declaration is not recursive, (2) the declaration has only one
    /// constructor, and (3) the type is declared with no indices.
    pub(crate) fn can_be_struct(&self, n: NameId) -> bool {
        self.get_structure(n, false).is_some()
    }

    pub(crate) fn get_structure(&self, n: NameId, rec_ok: bool) -> Option<&InductiveData> {
        match self.get_inductive(n) {
            Some(
                i @ InductiveData {
                    is_recursive,
                    num_indices,
                    all_ctor_names,
                    ..
                },
            ) if (all_ctor_names.len() == 1)
                && (*num_indices == 0)
                && (rec_ok || !is_recursive) =>
            {
                Some(i)
            }
            _ => None,
        }
    }

    /// Get the value of a declaration, if that declaration has an associated value (only
    /// definitions and theorems have values). Also returns the declaration's universe parameters.
    pub fn get_declar_val(&self, n: NameId) -> Option<(LevelsId, ExprId)> {
        match self.get_declar(n)? {
            Declar::Definition { info, val, .. } | Declar::Theorem { info, val, .. } => {
                Some((info.uparams, *val))
            }
            _ => None,
        }
    }
}

impl RecursorData {
    /// Get the name of the inductive type which is the major premise for this recursor
    /// by finding the correct binder in the recursor's type.
    pub fn get_major_induct(&self, ctx: &TcCtx<'_>) -> Option<NameId> {
        let binder = ctx.get_nth_pi_binder(self.info.ty, self.major_idx())?;
        match ctx.ex(ctx.unfold_apps_fun(binder)) {
            Expr::Const { name, .. } => Some(name),
            _ => None,
        }
    }
}
