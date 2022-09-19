use creusot_contracts::*;



#[trusted]
#[logic]
#[requires(false)]
#[ensures(false)]
pub fn unreachable<T>() -> T {
    absurd
}

#[logic]
#[requires(op != None)]
#[ensures(Some(result) == op)]
pub fn unwrap<T>(op: Option<T>) -> T {
    match op {
        Some(t) => t,
        None => unreachable()
    }
}

pub trait ToRef {
    // Hack to allow getting references in logical contexts
    #[logic]
    fn to_ref(&self) -> &Self {
        self
    }
}

impl<X: ?Sized> ToRef for X {}