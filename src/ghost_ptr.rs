// Inspired by https://plv.mpi-sws.org/rustbelt/ghostcell/ https://rust-unofficial.github.io/too-many-lists/fifth.html

use creusot_contracts::{prusti_prelude::*, logic::*, extern_spec};
use ::std::cell::UnsafeCell;
use ::std::marker::PhantomData;
use ::std::ptr::NonNull;
use ::std::ptr;
use ::std::alloc::{dealloc, Layout};
use crate::p_map::*;

/// Models a fragment of the heap that maps the [`GhostPtr`]s it has permission to their value.
/// At most one [`GhostToken`] has permission to each [`GhostPtr`]
/// No [`GhostToken`] has permission to a dangling [`GhostPtr`]
pub struct GhostToken<T: ?Sized>(Ghost<PMap<GhostPtr<T>, T>>, PhantomData<T>);

/// Thin wrapper over a raw pointer managed by a [`GhostPtr`]
pub type GhostPtr<T> = *mut T;


impl<T: ?Sized> ShallowModel for GhostToken<T> {
    type ShallowModelTy = PMap<GhostPtr<T>, T>;

    #[logic(('x) -> 'x)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        *self.0
    }
}

impl<T: ?Sized> GhostToken<T> {
    /// Creates a new [`GhostPtr`] that has no permission
    #[ensures(@result == PMap::empty())]
    pub fn new() -> Self {
        GhostToken(ghost!(PMap::empty()),PhantomData)
    }

    /// Gain permission to all of the [`GhostPtr`]s managed by other
    // Safety other cannot be accessed so it's pointers still only have one owner
    #[trusted]
    #[ensures(old(@self).disjoint(@other))]
    #[ensures((@*self) == old(@self).union(@other))]
    pub fn absorb(&mut self, other: GhostToken<T>) {}

    #[trusted]
    #[law('_, '_, '_)]
    #[requires((@self).contains(ptr1) && (@self).contains(ptr2))]
    #[requires(ptr1.addr_logic() == ptr2.addr_logic())]
    #[ensures(result)]
    #[ensures(result ==> ptr1 == ptr2)]
    fn injective_lemma(self, ptr1: GhostPtr<T>, ptr2: GhostPtr<T>) -> bool {
        absurd
    }

    /// Leaks memory iff the precondition fails
    #[requires((@self).is_empty())]
    pub fn drop(self) {}
}

impl<T: ?Sized> GhostPtrExt<T> for GhostPtr<T> {
    /// Creates a [`GhostPtr`] with initial value `val` and gives `t` permission to it
    // Safety this pointer was newly allocated no other GhostToken could have permission to it
    #[ensures(!old(@*t).contains(result))]
    #[ensures(@*t == old(@*t).insert(result, val))]
    fn new_in(val: T, t: &mut GhostToken<T>) -> Self
        where T: Sized {
        Self::from_box_in(Box::new(val), t)
    }

    #[ensures(@(result.1) == PMap::empty().insert(result.0, val))]
    fn new_pair(val: T) -> (Self, GhostToken<T>)
        where T: Sized {
        let mut t = GhostToken::new();
        (GhostPtr::new_in(val, &mut t), t)
    }

    /// Creates a null [`GhostPtr`] that no GhostToken has permission to
    // Safety even though this pointer is dangling no GhostToken has permission to it so it's okay
    #[trusted]
    #[ensures(result == Self::null_logic())]
    fn null() -> Self
        where T: Sized {
        ptr::null_mut()
    }

    /// Deallocates `self` and returns its stored value
    // Safety `self` is now dangling but since `t` doesn't have permission anymore no token does so this is okay
    #[requires((@*t).contains(self))]
    #[ensures(result == old(@*t).lookup(self))]
    #[ensures(@*t == old(@*t).remove(self))]
    fn take(self, t: &mut GhostToken<T>) -> T
        where T: Sized {
        *self.take_box(t)
    }

    /// Creates a [`GhostPtr`] with initial value `val` and gives `t` permission to it
    // Safety this pointer was newly allocated no other GhostToken could have permission to it
    #[trusted]
    #[ensures(!old(@*t).contains(result))]
    #[ensures(@*t == old(@*t).insert(result, *val))]
    fn from_box_in(val: Box<T>, t: &mut GhostToken<T>) -> Self {
        let ptr = Box::into_raw(val);
        unsafe { ptr }
    }

    #[trusted]
    #[logic(() -> '_)]
    #[ensures(forall<t: GhostToken<T>> !(@t).contains(result))]
    fn null_logic() -> Self {
        absurd
    }

    /// Immutably borrows `self`
    // Safety no other token has permission to `self`
    // `t` cannot be used to mutably borrow `self` as long as the shared lifetime lasts
    #[trusted]
    #[requires((@t).contains(self))]
    #[ensures(*result == *(@t).lookup_unsized(self))]
    fn borrow(self, t: &GhostToken<T>) -> &T {
        unsafe {&*self }
    }

    /// Mutably borrows `self` and returns a view of the rest of [`GhostPtrs`] stored in `t`
    // Safety no other token has permission to `self`
    // `t` cannot be used to borrow `self` as long as the mutable lifetime lasts
    // The returned token doesn't have access to `self` so it can't access it either
    #[trusted]
    #[requires((@**t).contains(self))]
    #[ensures(*result == *old(@**t).lookup_unsized(self))]
    #[ensures(@**t == old(@**t).remove(self))]
    #[after_expiry('i, @*old(*t) == (@*curr(*t)).insert(self, *result))]
    #[after_expiry('i, !(@*curr(*t)).contains(self))]
    fn reborrow<'o, 'i>(self, t: &'o mut &'i mut GhostToken<T>) -> &'i mut T {
        unsafe { &mut *self}
    }
    // (self, t: &mut GhostToken<T>) -> (&mut T, &mut GhostToken<T>)

    #[trusted] // shouldn't be needed
    #[requires((@*t).contains(self))]
    #[ensures(*result == *old(@*t).lookup_unsized(self))]
    #[after_expiry(@*t == old(@*t).insert(self, *result))]
    fn borrow_mut(self, t: &mut GhostToken<T>) -> &mut T {
        let mut t = t;
        self.reborrow(&mut t)
    }

    #[trusted]
    #[requires((@*t1).contains(self))]
    #[ensures(@*t1 == old(@*t1).remove(self))]
    #[ensures(@*t2 == old(@*t2).insert(self, *old(@t1).lookup_unsized(self)))]
    fn transfer(self, t1: &mut GhostToken<T>, t2: &mut GhostToken<T>) {}

    #[trusted]
    #[logic(('_) -> '_)]
    fn addr_logic(self) -> Int {
        absurd
    }

    /// Deallocates `self` and returns its stored value
    // Safety `self` is now dangling but since `t` doesn't have permission anymore no token does so this is okay
    #[trusted]
    #[requires((@*t).contains(self))]
    #[ensures(*result == *old(@*t).lookup_unsized(self))]
    #[ensures((@*t) == old(@*t).remove(self))]
    fn take_box(self, t: &mut GhostToken<T>) -> Box<T> {
        unsafe { Box::from_raw(self) }
    }
}

pub trait GhostPtrExt<T: ?Sized>: Sized {
    fn new_in(val: T, t: &mut GhostToken<T>) -> Self
    where T: Sized;
    fn new_pair(val: T) -> (Self, GhostToken<T>)
    where T: Sized;
    fn null() -> Self
    where T: Sized;
    fn take(self, t: &mut GhostToken<T>) -> T
    where T: Sized;
    fn from_box_in(val: Box<T>, t: &mut GhostToken<T>) -> Self;
    #[logic(() -> '_)]
    fn null_logic() -> Self;
    fn borrow(self, t: &GhostToken<T>) -> &T;
    fn reborrow<'o, 'i>(self, t: &'o mut &'i mut GhostToken<T>) -> &'i mut T;
    fn borrow_mut(self, t: &mut GhostToken<T>) -> &mut T;
    fn transfer(self, t1: &mut GhostToken<T>, t2: &mut GhostToken<T>);
    #[logic(('_) -> '_)]
    fn addr_logic(self) -> Int;
    fn take_box(self, t: &mut GhostToken<T>) -> Box<T>;
}

extern_spec!{
    impl<T> *mut T {
        // Safety since addr_logic is uninterpreted this just claims ptr::addr is deterministic
        #[trusted]
        #[ensures(@result == self.addr_logic())]
        fn addr(self) -> usize;

        /// Check if `self` was created with [`GhostPtr::null`]
        #[trusted]
        #[ensures(result == (self == GhostPtr::<T>::null_logic()))]
        fn is_null(self) -> bool;
    }
}

#[cfg_attr(not(feature = "contracts"), test)]
fn test() {
    let (ptr1, mut token) = GhostPtr::new_pair(5);
    let t = &mut token;
    let ptr2 = ptr1;
    proof_assert!((@t).contains(ptr1));
    let ptr3 = GhostPtr::new_in(7, t);
    proof_assert!((@t).contains(ptr1));
    let mut t_inner = &mut *t;
    let m1 = ptr1.reborrow(&mut t_inner);
    proof_assert!(@m1 == 5);
    proof_assert!(t_inner.shallow_model().lookup(ptr3) == 7i32);
    let r3 = ptr3.reborrow(&mut t_inner);
    // let bad = ptr2.borrow(t); // Borrow Checker Error
    // let bad = ptr2.borrow(t_inner); // Verification Error
    proof_assert!(@r3 == 7);
    *m1 = 10;
    let r2 = ptr2.borrow(t);
    // let bad = ptr3.borrow(t_inner); // Borrow Checker Error
    proof_assert!(@r2 == 10);
    // token.drop(); return; // Verification Error
    ptr1.take(t);
    // ptr2.take(t); // Verification Error
    ptr3.take(t);
    token.drop();
}

#[requires(token.shallow_model().contains(ptr1))]
#[requires(token.shallow_model().contains(ptr2))]
fn test2<T>(token: &mut GhostToken<T>, ptr1: GhostPtr<T>, ptr2: GhostPtr<T>) -> Option<(&mut T, &mut T)> {
    if ptr1.addr() != ptr2.addr() {
        proof_assert!(ptr1 != ptr2);
        proof_assert!((@token).remove(ptr1).get(ptr2) == (@token).get(ptr2));
        let mut t = &mut *token;
        let m1 = ptr1.reborrow(&mut t);
        let m2 = ptr2.borrow_mut(t);
        Some((m1, m2))
    } else {
        None
    }
}