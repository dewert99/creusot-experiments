use creusot_contracts::*;

pub trait Inv<T> {
    #[predicate]
    fn inv(&self, x: T) -> bool;
}

pub struct Cell<T, I> {
    inner: std::cell::Cell<T>,
    inv: I,
}

impl<T, I: Inv<T>> Cell<T, I> {
    #[trusted]
    #[requires(self.inv.inv(v))]
    #[ensures(self.inv.inv(result))]
    pub fn replace(&self, v: T) -> T {
        self.inner.replace(v)
    }

    #[logic]
    pub fn inv(self) -> I {
        self.inv
    }

    #[trusted]
    #[ensures(result.inv() == inv)]
    pub fn new(v: T, inv: I) -> Self {
        Cell{inv, inner: std::cell::Cell::new(v)}
    }
}