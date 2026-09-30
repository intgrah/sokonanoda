use super::hash::CowStr;
#[cfg(not(target_pointer_width = "64"))]
compile_error!("packed term pointers require a 64-bit target");
#[cfg(all(feature = "top-byte-ignore", not(target_arch = "aarch64")))]
compile_error!(
    "the `top-byte-ignore` feature requires the aarch64 target architecture (Top-Byte-Ignore)"
);

#[cfg(feature = "top-byte-ignore")]
const PTR_TAG: usize = 1 << 56;
#[cfg(not(feature = "top-byte-ignore"))]
const PTR_TAG: usize = 1;

use crate::term::expr::Expr;
use crate::term::level::Level;
use crate::term::name::Name;
use num_bigint::BigUint;
use std::marker::PhantomData;
use std::ptr::NonNull;

macro_rules! tagged_ptr {
    ($(#[$m:meta])* $name:ident, $pointee:ty) => {
        $(#[$m])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name<'a> {
            ptr: NonNull<$pointee>,
            _ph: PhantomData<&'a $pointee>,
        }

        unsafe impl<'a> Send for $name<'a> {}
        unsafe impl<'a> Sync for $name<'a> {}

        impl<'a> $name<'a> {
            #[inline]
            pub(crate) fn global(r: &'a $pointee) -> Self {
                Self { ptr: NonNull::from(r), _ph: PhantomData }
            }

            #[inline]
            pub(crate) fn local(r: &'a $pointee) -> Self {
                let tagged = NonNull::from(r).as_ptr().map_addr(|a| a | PTR_TAG);
                Self { ptr: unsafe { NonNull::new_unchecked(tagged) }, _ph: PhantomData }
            }

            #[inline]
            pub(crate) fn is_local(self) -> bool { self.ptr.as_ptr().addr() & PTR_TAG != 0 }

            #[cfg(feature = "top-byte-ignore")]
            #[inline]
            pub(crate) fn as_ref(self) -> &'a $pointee { unsafe { &*self.ptr.as_ptr() } }
            #[cfg(not(feature = "top-byte-ignore"))]
            #[inline]
            pub(crate) fn as_ref(self) -> &'a $pointee {
                unsafe { &*self.ptr.as_ptr().map_addr(|a| a & !PTR_TAG) }
            }

            #[inline]
            pub(crate) fn get_hash(&self) -> u64 { self.ptr.as_ptr().addr() as u64 }

            #[inline]
            #[allow(dead_code)]
            pub(crate) fn into_raw(self) -> NonNull<$pointee> { self.ptr }

            #[inline]
            #[allow(dead_code)]
            pub(crate) unsafe fn from_raw(ptr: NonNull<$pointee>) -> Self {
                Self { ptr, _ph: PhantomData }
            }
        }

        impl<'a> std::ops::Deref for $name<'a> {
            type Target = $pointee;
            #[inline]
            fn deref(&self) -> &$pointee { self.as_ref() }
        }

        impl<'a> std::fmt::Debug for $name<'a> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({:p}{})", stringify!($name), self.as_ref(), if self.is_local() { ",L" } else { "" })
            }
        }
    };
}

tagged_ptr!(StringPtr, CowStr<'a>);
tagged_ptr!(NamePtr, crate::term::name::NameNode<'a>);
tagged_ptr!(LevelPtr, Level<'a>);
tagged_ptr!(BigUintPtr, BigUint);

const EXPR_ADDR_MASK: u64 = 0x0000_ffff_ffff_fff8;
const EXPR_LOCAL_BIT: u64 = 1;
const EXPR_BVAR_SHIFT: u32 = 48;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprPtr<'a> {
    bits: std::num::NonZeroU64,
    _ph: PhantomData<&'a Expr<'a>>,
}

unsafe impl Send for ExprPtr<'_> {}
unsafe impl Sync for ExprPtr<'_> {}

impl<'a> ExprPtr<'a> {
    #[inline]
    fn pack(r: &'a Expr<'a>, tag: u64) -> Self {
        let addr = std::ptr::from_ref(r) as usize as u64;
        assert!(addr & !EXPR_ADDR_MASK == 0);
        let derived = u64::from(r.num_loose_bvars()) << EXPR_BVAR_SHIFT;
        Self {
            bits: unsafe { std::num::NonZeroU64::new_unchecked(addr | tag | derived) },
            _ph: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn global(r: &'a Expr<'a>, num_loose_bvars: u16) -> Self {
        let addr = std::ptr::from_ref(r) as usize as u64;
        assert!(addr & !EXPR_ADDR_MASK == 0);
        debug_assert_eq!(num_loose_bvars, r.num_loose_bvars());
        let bits = addr | (u64::from(num_loose_bvars) << EXPR_BVAR_SHIFT);
        Self {
            bits: unsafe { std::num::NonZeroU64::new_unchecked(bits) },
            _ph: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn local(r: &'a Expr<'a>) -> Self {
        Self::pack(r, EXPR_LOCAL_BIT)
    }

    #[inline]
    pub(crate) fn is_local(self) -> bool {
        self.bits.get() & EXPR_LOCAL_BIT != 0
    }

    #[inline]
    pub(crate) fn num_loose_bvars(self) -> u16 {
        (self.bits.get() >> EXPR_BVAR_SHIFT) as u16
    }

    #[inline]
    pub(crate) fn addr(self) -> usize {
        (self.bits.get() & EXPR_ADDR_MASK) as usize
    }

    #[inline]
    pub(crate) fn as_ref(self) -> &'a Expr<'a> {
        unsafe { &*(self.addr() as *const Expr<'a>) }
    }
}

impl<'a> std::ops::Deref for ExprPtr<'a> {
    type Target = Expr<'a>;
    #[inline]
    fn deref(&self) -> &Expr<'a> {
        self.as_ref()
    }
}

impl std::fmt::Debug for ExprPtr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ExprPtr({:p}{})",
            self.as_ref(),
            if self.is_local() { ",L" } else { "" }
        )
    }
}

const _: () = assert!(std::mem::align_of::<Expr<'static>>() >= 8);
const _: () = assert!(std::mem::size_of::<Option<ExprPtr<'static>>>() == 8);
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<Name<'static>>() >= 2);
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<Level<'static>>() >= 2);
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<CowStr<'static>>() >= 2);
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<BigUint>() >= 2);
#[cfg(not(feature = "top-byte-ignore"))]
const _: () = assert!(std::mem::align_of::<LevelPtr<'static>>() >= 2);

const LEVELS_ADDR_MASK: u64 = 0x0000_ffff_ffff_ffff;
const LEVELS_TAG: u64 = 1 << 63;
const LEVELS_LEN_SHIFT: u32 = 48;
const LEVELS_LEN_MAX: usize = (1 << 15) - 1;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct LevelsPtr<'a> {
    bits: std::num::NonZeroU64,
    _ph: PhantomData<&'a [LevelPtr<'a>]>,
}

impl<'a> LevelsPtr<'a> {
    #[inline]
    fn pack(s: &'a [LevelPtr<'a>], tag: u64) -> Self {
        let addr = s.as_ptr() as usize as u64;
        assert!(
            addr & !LEVELS_ADDR_MASK == 0,
            "level slice address exceeds 48 bits"
        );
        assert!(
            s.len() <= LEVELS_LEN_MAX,
            "universe parameter list too long"
        );
        let bits = addr | ((s.len() as u64) << LEVELS_LEN_SHIFT) | tag | 1;
        Self {
            bits: unsafe { std::num::NonZeroU64::new_unchecked(bits) },
            _ph: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn global(s: &'a [LevelPtr<'a>]) -> Self {
        Self::pack(s, 0)
    }

    #[inline]
    pub(crate) fn local(s: &'a [LevelPtr<'a>]) -> Self {
        Self::pack(s, LEVELS_TAG)
    }

    #[inline]
    pub(crate) fn len(self) -> usize {
        ((self.bits.get() >> LEVELS_LEN_SHIFT) & 0x7fff) as usize
    }

    #[inline]
    pub(crate) fn as_ref(self) -> &'a [LevelPtr<'a>] {
        let p = (self.bits.get() & LEVELS_ADDR_MASK & !1) as usize as *const LevelPtr<'a>;
        unsafe { std::slice::from_raw_parts(p, self.len()) }
    }

    #[inline]
    pub(crate) fn get_hash(self) -> u64 {
        self.bits.get()
    }
}

unsafe impl Send for LevelsPtr<'_> {}
unsafe impl Sync for LevelsPtr<'_> {}

impl<'a> std::ops::Deref for LevelsPtr<'a> {
    type Target = [LevelPtr<'a>];
    #[inline]
    fn deref(&self) -> &[LevelPtr<'a>] {
        self.as_ref()
    }
}
impl std::fmt::Debug for LevelsPtr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LevelsPtr({:?})", self.as_ref())
    }
}

pub struct Id<'a, T>(&'a T);

impl<'a, T> Id<'a, T> {
    #[inline]
    pub(crate) fn of(r: &'a T) -> Self {
        Self(r)
    }

    #[inline]
    pub(crate) fn addr(self) -> usize {
        std::ptr::from_ref(self.0).addr()
    }
}

impl<T> Clone for Id<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for Id<'_, T> {}

impl<T> PartialEq for Id<'_, T> {
    #[inline]
    fn eq(&self, o: &Self) -> bool {
        std::ptr::eq(self.0, o.0)
    }
}
impl<T> Eq for Id<'_, T> {}

impl<T> PartialOrd for Id<'_, T> {
    #[inline]
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}
impl<T> Ord for Id<'_, T> {
    #[inline]
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        self.addr().cmp(&o.addr())
    }
}

impl<T> std::hash::Hash for Id<'_, T> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_usize(self.addr());
    }
}

impl<T> std::fmt::Debug for Id<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Id({:p})", self.0)
    }
}
