use creusot_contracts::*;
use super::transmute::*;

pub trait Inv<T: ?Sized> {

    #[predicate]
    fn invariant(self, target: T) -> bool;
}

//#[invariant(self.inv.invariant(self.data))]
#[repr(transparent)]
pub struct InvGuard<I: Inv<T>, T: ?Sized> {
    inv: Ghost<I>, // final
    pub(crate) data: T,
}

pub struct CreateInv<I>(Ghost<I>);

unsafe impl<I: Inv<T>, T: ?Sized> TransmuteFn<T> for CreateInv<I> {
    type Output = InvGuard<I, T>;

    #[predicate]
    fn precondition(self, arg: T) -> bool {
        self.0.invariant(arg)
    }

    #[predicate]
    fn postcondition(self, arg: T, res: Self::Output) -> bool {
        res.inv == self.0 && res.data == arg
    }
}

pub struct StripInv;

unsafe impl<I: Inv<T>, T: ?Sized> TransmuteFn<InvGuard<I, T>> for StripInv {
    type Output = T;

    #[predicate]
    fn precondition(self, arg: InvGuard<I, T>) -> bool {
        true
    }

    #[predicate]
    fn postcondition(self, arg: InvGuard<I, T>, res: Self::Output) -> bool {
        arg.inv.invariant(arg.data) && res == arg.data
    }
}

impl<I: Inv<T>, T: ?Sized> InvGuard<I, T> {
    #[trusted]// Safety the inv field is private and we never change it
    #[law]
    #[ensures((*self).inv == (^self).inv)]
    pub fn inv_final_lemma(&mut self) {
        absurd
    }

    #[logic]
    pub fn inv(&self) -> I {
        *self.inv
    }
}

pub struct CanTransmuteInv<F>(F);

impl<T: ?Sized, F: TransmuteFn<T>> Inv<T> for CanTransmuteInv<F> {
    #[predicate]
    fn invariant(self, target: T) -> bool {
        self.0.precondition(target)
    }
}

#[requires(t1.precondition(*from))]
#[requires(forall<input: &T, output: &F1::Output> t1.postcondition(*input, *output) ==> t2.precondition(*output))]
#[ensures(t1.postcondition(*from, (*result).data))]
#[ensures(t2.postcondition((^result).data, ^from))]
pub fn transmute_to_guard<T, F1, F2>(t1: F1, t2: F2, from: &mut T) -> &mut InvGuard<CanTransmuteInv<F2>, F1::Output>
    where F1: TransmuteFn<T>, F2: TransmuteFn<F1::Output, Output=T> {
    InvGuard::<CanTransmuteInv<F2>, F1::Output>::inv_final_lemma;
    let there = TransTFn(t1, CreateInv(ghost!(CanTransmuteInv(t2))));
    let back = TransTFn(StripInv, t2);
    proof_assert!(there.precondition(*from));
    //proof_assert!(forall <res: &mut InvGuard<CanTransmuteInv<F2>, F1::Output>> (*res).inv.invariant((*res).data) ==> back.precondition(^res));
    transmute(MutTFn(there, back), from)
}

#[requires(inv.invariant(*from))]
#[ensures(inv.invariant(^from))]
#[ensures((*result).data == *from)]
#[ensures((^result).data == ^from)]
#[ensures((*result).inv == inv)]
pub fn guard_inv<T, I: Inv<T>>(inv: Ghost<I>, from: &mut T) -> &mut InvGuard<I, T> {
    InvGuard::<I, T>::inv_final_lemma;
    transmute(MutTFn(CreateInv(inv), StripInv), from)
}