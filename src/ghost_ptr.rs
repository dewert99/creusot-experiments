// Inspired by https://plv.mpi-sws.org/rustbelt/ghostcell/ https://rust-unofficial.github.io/too-many-lists/fifth.html

use creusot_contracts::*;
use ::std::cell::UnsafeCell;
use ::std::marker::PhantomData;
use ::std::ptr::NonNull;
use ::std::ptr;
use ::std::alloc::{dealloc, Layout};
use crate::p_map::*;

/// Models a fragment of the heap that maps the [`GhostPtr`]s it has permission to their value.
/// At most one [`GhostToken`] has permission to each [`GhostPtr`]
/// No [`GhostToken`] has permission to a dangling [`GhostPtr`]
#[trusted] // Means opaque in this context
pub struct GhostToken<T: ?Sized>(PhantomData<T>);

/// Thin wrapper over a raw pointer managed by a [`GhostPtr`]
pub struct GhostPtr<T: ?Sized>(*mut T);

impl<T: ?Sized> Copy for GhostPtr<T> {}

impl<T: ?Sized> Clone for GhostPtr<T> {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}


impl<T: ?Sized> Model for GhostToken<T> {
    type ModelTy = PMap<GhostPtr<T>, T>;

    #[trusted]
    #[logic]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}

impl<T: ?Sized> GhostToken<T> {
    /// Creates a new [`GhostPtr`] that has no permission
    #[trusted]
    #[ensures(@result == PMap::empty())]
    pub fn new() -> Self {
        GhostToken(PhantomData::default())
    }

    /// Gain permission to all of the [`GhostPtr`]s managed by other
    // Safety other cannot be accessed so it's pointers still only have one owner
    #[trusted]
    #[ensures((@*self).disjoint(@other))]
    #[ensures((@^self) == (@*self).union(@other))]
    pub fn absorb(&mut self, other: GhostToken<T>) {}

    /// Leaks memory iff the precondition fails
    #[requires((@self).is_empty())]
    pub fn drop(self) {}
}

impl<T> GhostPtr<T> {
    /// Creates a [`GhostPtr`] with initial value `val` and gives `t` permission to it
    // Safety this pointer was newly allocated no other GhostToken could have permission to it
    #[ensures(! (@*t).contains(result))]
    #[ensures(@^t == (@*t).insert(result, val))]
    pub fn new_in(val: T, t: &mut GhostToken<T>) -> Self {
        Self::from_box_in(Box::new(val), t)
    }

    #[ensures(@(result.1) == PMap::empty().insert(result.0, val))]
    pub fn new_pair(val: T) -> (Self, GhostToken<T>) {
        let mut t = GhostToken::new();
        (GhostPtr::new_in(val, &mut t), t)
    }

    /// Creates a null [`GhostPtr`] that no GhostToken has permission to
    // Safety even though this pointer is dangling no GhostToken has permission to it so it's okay
    #[trusted]
    #[ensures(result == Self::null_logic())]
    pub fn null() -> Self {
        GhostPtr(ptr::null_mut())
    }

    /// Deallocates `self` and returns its stored value
    // Safety `self` is now dangling but since `t` doesn't have permission anymore no token does so this is okay
    #[requires((@*t).contains(self))]
    #[ensures(result == (@*t).lookup(self))]
    #[ensures((@^t) == (@*t).remove(self))]
    pub fn take(self, t: &mut GhostToken<T>) -> T {
        *self.take_box(t)
    }
}

impl<T: ?Sized> GhostPtr<T> {

    /// Creates a [`GhostPtr`] with initial value `val` and gives `t` permission to it
    // Safety this pointer was newly allocated no other GhostToken could have permission to it
    #[trusted]
    #[ensures(!(@*t).contains(result))]
    #[ensures(@^t == (@*t).insert(result, *val))]
    pub fn from_box_in(val: Box<T>, t: &mut GhostToken<T>) -> Self {
        let ptr = Box::into_raw(val);
        unsafe { GhostPtr(ptr) }
    }

    /// Check if `self` was created with [`GhostPtr::null`]
    #[trusted]
    #[ensures(result == (self == Self::null_logic()))]
    pub fn is_null(self) -> bool {
        self.0.is_null()
    }

    #[trusted]
    #[logic]
    #[ensures(forall<t: GhostToken<T>> !(@t).contains(result))]
    pub fn null_logic() -> Self {
        absurd
    }

    /// Immutably borrows `self`
    // Safety no other token has permission to `self`
    // `t` cannot be used to mutably borrow `self` as long as the shared lifetime lasts
    #[trusted]
    #[requires((@t).contains(self))]
    #[ensures(*result == *(@t).lookup_ghost(self))]
    pub fn borrow(self, t: &GhostToken<T>) -> &T {
        unsafe {&*self.0 }
    }

    /// Mutably borrows `self` and returns a view of the rest of [`GhostPtrs`] stored in `t`
    // Safety no other token has permission to `self`
    // `t` cannot be used to borrow `self` as long as the mutable lifetime lasts
    // The returned token doesn't have access to `self` so it can't access it either
    #[trusted]
    #[requires((@**t).contains(self))]
    #[ensures(*result == *(@**t).lookup_ghost(self))]
    #[ensures(@*^t == (@**t).remove(self))]
    #[ensures(@^*t == (@^^t).insert(self, ^result))]
    pub fn reborrow<'o, 'i>(self, t: &'o mut &'i mut GhostToken<T>) -> &'i mut T {
        unsafe { &mut *self.0}
    }
    // (self, t: &mut GhostToken<T>) -> (&mut T, &mut GhostToken<T>)

    #[trusted] // shouldn't be needed
    #[requires((@*t).contains(self))]
    #[ensures(*result == *(@*t).lookup_ghost(self))]
    #[ensures(@^t == (@*t).insert(self, ^result))]
    pub fn borrow_mut(self, t: &mut GhostToken<T>) -> &mut T {
        let mut t = t;
        self.reborrow(&mut t)
    }

    #[trusted]
    #[requires((@*t1).contains(self))]
    #[ensures(@^t1 == (@^t1).remove(self))]
    #[ensures(@^t2 == (@^t2).insert(self, *(@*t1).lookup_ghost(self)))]
    pub fn transfer(self, t1: &mut GhostToken<T>, t2: &mut GhostToken<T>) {}

    #[trusted]
    #[logic]
    pub fn addr_logic(self) -> Int {
        absurd
    }

    // Safety since addr_logic is uninterpreted this just claims ptr::addr is deterministic
    #[trusted]
    #[ensures(@result == self.addr_logic())]
    pub fn addr(self) -> usize {
        self.0.to_raw_parts().0 as usize
    }

    /// Deallocates `self` and returns its stored value
    // Safety `self` is now dangling but since `t` doesn't have permission anymore no token does so this is okay
    #[trusted]
    #[requires((@*t).contains(self))]
    #[ensures(*result == *(@*t).lookup_ghost(self))]
    #[ensures((@^t) == (@*t).remove(self))]
    pub fn take_box(self, t: &mut GhostToken<T>) -> Box<T> {
        unsafe { Box::from_raw(self.0) }
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
    proof_assert!(t_inner.model().lookup(ptr3) == 7i32);
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

#[requires(token.model().contains(ptr1))]
#[requires(token.model().contains(ptr2))]
fn test2<T>(token: &mut GhostToken<T>, ptr1: GhostPtr<T>, ptr2: GhostPtr<T>) -> Option<(&mut T, &mut T)> {
    if ptr1.addr() != ptr2.addr() {
        proof_assert!(ptr1 != ptr2);
        proof_assert!(token.model().remove(ptr1).get(ptr2) == token.model().get(ptr2));
        let mut t = &mut *token;
        let m1 = ptr1.reborrow(&mut t);
        let m2 = ptr2.borrow_mut(t);
        Some((m1, m2))
    } else {
        None
    }
}