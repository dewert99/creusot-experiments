use ::std::mem;
use ::std::marker::PhantomData;
use ::std::num::NonZeroU32;
use creusot_contracts::*;

/// Safety it must be safe to transmute in -> out where precondition(in) holds
/// This must also guarantee postcondition(in, out) holds
pub unsafe trait TransmuteFn<X> {
    type Output;

    #[predicate]
    fn precondition(arg: X) -> bool;

    #[predicate]
    #[requires(Self::precondition(arg))]
    fn postcondition(arg: X, res: Self::Output) -> bool;
}

pub struct IdTFn;
// Safety transmute doesn't do anything
unsafe impl<X: PartialEq> TransmuteFn<X> for IdTFn {
    type Output = X;

    #[predicate]
    fn precondition(arg: X) -> bool {
        true
    }

    #[predicate]
    #[requires(Self::precondition(arg))]
    fn postcondition(arg: X, res: Self::Output) -> bool {
        res == arg
    }
}

pub struct TransTFn<T0, T1>(T0, T1);
unsafe impl<X, T0: TransmuteFn<X>, T1: TransmuteFn<T0::Output>> TransmuteFn<X> for TransTFn<T0, T1> {
    type Output = T1::Output;

    #[predicate]
    fn precondition(arg: X) -> bool {
        pearlite! {
            T0::precondition(arg) && forall<mid: T0::Output> T0::postcondition(arg, mid) ==> T1::precondition(mid)
        }
    }

    #[predicate]
    //#[requires(Self::precondition(arg))] https://github.com/xldenis/creusot/issues/266
    fn postcondition(arg: X, res: Self::Output) -> bool {
        pearlite! {
            exists<mid: T0::Output> T0::postcondition(arg, mid) && T1::postcondition(mid, res)
        }
    }
}

pub struct RefTFn<T0>(T0);
unsafe impl<'a, X: 'a, T0: TransmuteFn<X>> TransmuteFn<&'a X> for RefTFn<T0>
where T0::Output: 'a {
    type Output = &'a T0::Output;

    #[predicate]
    fn precondition(arg: &'a X) -> bool {
        T0::precondition(*arg)
    }

    #[predicate]
    #[requires(Self::precondition(arg))]
    fn postcondition(arg: &'a X, res: Self::Output) -> bool {
        T0::postcondition(*arg, *res)
    }
}

pub struct MutTFn<T0, T1=T0>(T0, T1);
unsafe impl<'a, X: 'a, T0: TransmuteFn<X>, T1: TransmuteFn<T0::Output, Output=X>> TransmuteFn<&'a mut X> for MutTFn<T0, T1>
    where T0::Output: 'a {
    type Output = &'a mut T0::Output;

    #[predicate]
    fn precondition(arg: &'a mut X) -> bool {
        T0::precondition(*arg) && pearlite!{forall<future: T0::Output> T1::precondition(future)}
    }

    #[predicate]
    #[requires(Self::precondition(arg))]
    fn postcondition(arg: &'a mut X, res: Self::Output) -> bool {
        T0::postcondition(*arg, *res) && pearlite!{T1::postcondition(^res, ^arg)}
    }
}

struct NonZeroTFn;
// Safety NonZeroU32 has #[repr(transparent)] and it's only niche is 0
unsafe impl TransmuteFn<u32> for NonZeroTFn {
    type Output = NonZeroU32;

    #[predicate]
    fn precondition(arg: u32) -> bool {
        arg.model() != 0
    }

    #[predicate]
    #[requires(Self::precondition(arg))]
    fn postcondition(arg: u32, res: Self::Output) -> bool {
        true // res.get() == arg
    }
}

unsafe impl TransmuteFn<NonZeroU32> for NonZeroTFn {
    type Output = u32;

    #[predicate]
    fn precondition(arg: NonZeroU32) -> bool {
        true
    }

    #[predicate]
    #[requires(Self::precondition(arg))]
    fn postcondition(arg: NonZeroU32, res: Self::Output) -> bool {
        true // res == arg.get()
    }
}

#[repr(C)]
struct CPair<X, Y>(pub X, pub Y);

struct CPairTFn<T0, T1>(T0, T1);

// Safety CPair has #[repr(C)] and T0/T1 make sure it's safe to transmute it's children
unsafe impl<X0, X1, T0: TransmuteFn<X0>, T1: TransmuteFn<X1>> TransmuteFn<CPair<X0, X1>> for CPairTFn<T0, T1> {
    type Output = CPair<T0::Output, T1::Output>;

    #[predicate]
    fn precondition(arg: CPair<X0, X1>) -> bool {
        T0::precondition(arg.0) && T1::precondition(arg.1)
    }

    #[predicate]
    #[requires(Self::precondition(arg))]
    fn postcondition(arg: CPair<X0, X1>, res: Self::Output) -> bool {
        T0::postcondition(arg.0, res.0) && T1::postcondition(arg.1, res.1)
    }
}



#[trusted]
#[requires(T::precondition(from))]
#[ensures(T::postcondition(from, result))]
pub fn transmute<X: Sized, T: TransmuteFn<X>>(from: X) -> T::Output {
    // Safety T is an unsafe trait who's implementer made sure this was safe
    unsafe {
        let to = mem::transmute_copy(&from);
        mem::forget(from);
        to
    }
}

fn test1() {
    let x = CPair(true, 1);
    let y = transmute::<_,CPairTFn<IdTFn, NonZeroTFn>>(x);
    assert!(y.0)
}

fn test2() {
    let mut x = CPair(true, 0);
    // let yr = transmute::<_,MutTFn<CPairTFn<IdTFn, NonZeroTFn>>>(&mut x); // Should fail
}

#[ensures((^x).0 == false)]
fn set_false(x: &mut CPair<bool, NonZeroU32>) {
    x.0 = false;
}

fn test3() {
    let mut x = CPair(true, 1);
    let yr: &mut CPair<bool, NonZeroU32> = transmute::<_,MutTFn<CPairTFn<IdTFn, NonZeroTFn>>>(&mut x);
    assert!(yr.0);
    set_false(yr);
    proof_assert!(!x.0)
}

fn test4() {
    let x = CPair(true, 1);
    let mut x = transmute::<_,CPairTFn<IdTFn, NonZeroTFn>>(x);
    // let yr: &mut CPair<bool, u32> = transmute::<_,MutTFn<CPairTFn<IdTFn, NonZeroTFn>>>(&mut x); //should fail
}