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
