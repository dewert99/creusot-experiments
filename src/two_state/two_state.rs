use creusot_contracts::*;
use creusot_contracts::std::ops::FnOnceExt;

pub trait PreOrd {
    #[logic]
    fn le(self, oth: Self) -> bool;

    #[law]
    #[ensures(self.le(self))]
    fn refl(self);

    #[law]
    #[ensures(self.le(mid) ==> mid.le(end) ==> self.le(end))]
    fn trans(self, mid: Self, end: Self);
}

pub struct TwoState<T: PreOrd>{
    id: Ghost<Int>,
    data: T
}

pub struct TwoStateToken<T: PreOrd>{
    id: Ghost<Int>,
    data: Ghost<T>,
}

impl<T: PreOrd> Clone for TwoStateToken<T> {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: PreOrd> Copy for TwoStateToken<T> {}


impl<T: PreOrd> TwoStateToken<T> {
    #[logic]
    pub fn id(self) -> Int {
        *self.id
    }

    #[logic]
    pub fn value(self) -> T {
        *self.data
    }
}

impl<T: PreOrd> TwoState<T> {
    #[logic]
    pub fn id(self) -> Int {
        *self.id
    }

    #[logic]
    pub fn value(self) -> T {
        self.data
    }

    #[trusted]
    #[logic] // Should be predicate
    #[ensures((*self).value() == *result)]
    #[ensures((^self).value() == ^result)]
    pub fn value_mut(&mut self) -> &mut T {
        absurd
    }

    #[trusted]
    #[ensures(result.0.value() == val)]
    #[ensures(result.0.value() == result.1.value())]
    #[ensures(result.0.id() == result.1.id())]
    pub fn new_with_token(val: T) -> (Self, TwoStateToken<T>) {
        let gval = ghost!(val);
        let id = ghost!(0.deep_model()); // this isn't accurate (note the trusted)
        (TwoState { id, data: val }, TwoStateToken { id, data: gval })
    }

    #[trusted]
    #[requires(f.precondition((self.value_mut(),)))]
    #[requires(f.postcondition_once((self.value_mut(),), ()) ==> (*self).value().le((^self).value()))]
    #[ensures(f.postcondition_once((self.value_mut(),), ()))]
    #[ensures((^self).id() == (*self).id())]
    #[ensures(result.id() == (*self).id() && result.value() == (^self).value())]
    pub fn update<F: FnOnce(&mut T)>(&mut self, f: F) -> TwoStateToken<T> {
        f(&mut self.data);
        TwoStateToken{id: self.id, data: ghost!(self.data)}
    }

    #[ensures((*self).value() == *result)]
    #[ensures((^self).value() == ^result)]
    // Doesn't #[ensures(^self.id() == *self.id())]
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.data
    }

    #[ensures(*result == self.value())]
    pub fn get(&self) -> &T {
        &self.data
    }

    #[trusted]
    #[requires(self.id() == tok.id())]
    #[ensures(tok.value().le(self.value()))]
    pub fn check_token(&self, tok: TwoStateToken<T>) {}
}