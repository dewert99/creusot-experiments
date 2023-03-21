use creusot_contracts::*;
use crate::two_state::cell::{Cell, Inv};
use crate::two_state::two_state::*;

pub struct TwoStateInv(Ghost<Int>);

impl<T: PreOrd> Inv<Option<TwoState<T>>> for TwoStateInv {
    #[predicate]
    fn inv(&self, x: Option<TwoState<T>>) -> bool {
        match x {
            Some(x) => x.id() == *self.0,
            None => true
        }
    }
}

pub struct TwoStateCell<T: PreOrd>(Cell<Option<TwoState<T>>, TwoStateInv>);

impl<T: PreOrd> TwoStateCell<T> {
    #[logic]
    pub fn id(&self) -> Int {
        *(self.0.inv().0)
    }

    #[ensures(result.0.id() == result.1.id())]
    #[ensures(result.1.value() == v)]
    pub fn new(v: T) -> (Self, TwoStateToken<T>) {
        let (ts, tok) = TwoState::new_with_token(v);
        proof_assert!(ts.id() == tok.id());
        let g = ghost!(ts.id());
        (TwoStateCell(Cell::new(Some(ts), TwoStateInv(g))), tok)
    }

    #[ensures(match result {Some(ts) => ts.id() == self.id(), None => true})]
    pub fn try_take(&self) -> Option<TwoState<T>> {
        self.0.replace(None)
    }

    #[ensures(result.id() == self.id())]
    pub fn take(&self) -> TwoState<T> {
        self.try_take().unwrap() // Can't prove that this doesn't panic
    }

    #[requires(val.id() == self.id())]
    pub fn put_back(&self, val: TwoState<T>) {
        self.0.replace(Some(val));
    }
}