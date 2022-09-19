use ::std::marker::PhantomData;
use creusot_contracts::*;
use owned_drop::*;
use ::std::mem::{forget, ManuallyDrop};
use creusot_contracts::std::FnOnceSpec;
use crate::mem::uninit::MaybeUninitTFn;
use super::invariant_transmute::*;


pub trait DropGuardFn<'a, T> {
    #[predicate]
    fn postcondition(self, arg: &mut T) -> bool;

    /// May panic but must always be memory safe and otherwise make sure the postcondition holds
    #[ensures(self.postcondition(arg))]
    fn drop_arg(self, arg: &'a mut T);
}

pub struct Abort;

impl<'a, T> DropGuardFn<'a, T> for Abort {

    #[predicate]
    fn postcondition(self, arg: &mut T) -> bool {
        false
    }

    #[trusted]
    #[ensures(false)]
    fn drop_arg(self, arg: &'a mut T) {
        panic!("Aborting due to panic in while handling invalid state")
    }
}


pub struct DropGuardInner<'a, T, F: DropGuardFn<'a, T> = Abort> {
    data: &'a mut T,
    drop_fn: F,
}

type DropGuard<'a, T, F = Abort> = OwnedDropWrapper<DropGuardInner<'a, T, F>>;

impl<'a, T, F: DropGuardFn<'a, T>> OwnedDrop for DropGuardInner<'a, T, F> {
    // Must only be run during unwinding
    #[trusted]
    fn drop(self) {
        let DropGuardInner{mut drop_fn, mut data, ..} = self;
        // Tries to call drop_arg to restore the invariant
        // If it panics rust will abort since we are unwinding
        drop_fn.drop_arg(data);
    }
}

#[trusted]
#[requires(forall <state: &mut T> drop_fn.postcondition(state) ==> from.inv().invariant(^state))]
#[requires(forall <state: &mut T> (*from).data == *state ==> f.precondition((state,)))]
#[requires(forall <state: &mut T> (*from).data == *state && f.postcondition_once((state,), ())
    ==> from.inv().invariant(^state))]
#[ensures(exists <state: &mut T> (*from).data == *state && (^from).data == ^state &&
    f.postcondition_once((state,), ()))]
pub fn drop_guard<'a, T: 'a, I, D, F>(from: &'a mut InvGuard<I, T>, f: F, drop_fn: D)
    where I: Inv<T>, D: DropGuardFn<'a, T>, F: FnOnce(&mut T) {
    let data = &mut from.data;
    let mut guard = DropGuard::new(DropGuardInner{data, drop_fn});
    f(&mut *guard.data);
    drop(guard.into_inner());
}

#[requires(forall <state: &mut T> (*from).data == *state ==> f.precondition((state,)))]
#[requires(forall <state: &mut T> (*from).data == *state && f.postcondition_once((state,), ())
    ==> from.inv().invariant(^state))]
#[ensures(exists <state: &mut T> (*from).data == *state && (^from).data == ^state &&
    f.postcondition_once((state,), ()))]
pub fn abort_drop_guard<'a, T: 'a, I, F>(from: &'a mut InvGuard<I, T>, f: F)
    where I: Inv<T>, F: FnOnce(&mut T) {
    drop_guard(from, f,Abort)
}

#[requires(f.precondition((*data,)))]
#[ensures(f.postcondition_once((*data,), ^data))]
fn replace_with<T, F: FnOnce(T) -> T>(data: &mut T, f: F) {
    use super::uninit::*;
    let g = transmute_to_guard(MaybeUninitTFn, AssumeInitTFn, data);
    let inner_f =
        #[requires((*x).is_init())]
        #[requires(f.precondition(((*x).unwrap(),)))]
        #[ensures((^x).is_init())]
        #[ensures(f.postcondition_once(((*x).unwrap(),), (^x).unwrap()))]
        |x: &mut MaybeUninit<T>| {
            let input = x.take();
            let output = f(input);
            x.write(output);
        };
    abort_drop_guard(g, inner_f);
}