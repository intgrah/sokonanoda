// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

pub(crate) const LOCAL: u32 = 1 << 31;

macro_rules! ids {
    ($($name:ident),*) => {
        $(
            #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
            pub struct $name(u32);

            impl $name {
                #[inline(always)]
                pub(crate) fn new(index: u32, local: bool) -> Self {
                    assert!(index < LOCAL, "term store exceeds 2^31 entries");
                    Self(if local { index | LOCAL } else { index })
                }

                #[inline(always)]
                pub(crate) fn is_local(self) -> bool {
                    self.0 & LOCAL != 0
                }

                #[inline(always)]
                pub(crate) fn index(self) -> usize {
                    (self.0 & !LOCAL) as usize
                }

                #[inline(always)]
                pub(crate) fn raw(self) -> u32 {
                    self.0
                }

                #[inline(always)]
                pub(crate) fn from_raw(raw: u32) -> Self {
                    Self(raw)
                }
            }
        )*
    };
}

ids!(ExprId, NameId, LevelId, LevelsId, StrId, BigId);

pub(crate) const ANON: NameId = NameId(0);
pub(crate) const ZERO: LevelId = LevelId(0);
