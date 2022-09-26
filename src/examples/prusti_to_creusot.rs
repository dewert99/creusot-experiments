use creusot_contracts::*;
use crate::helpers::unwrap;

#[logic]
fn last<T>(v: Vec<T>) -> Option<T> {
    if v.model().len() == 0 {None} else {Some(v.model().last())}
}

#[requires(last(*vec1) != None)]
#[requires(*unwrap(last(*vec1)) < 100u32)]
#[ensures(*unwrap(last(^vec2)) == 1u32 + *unwrap(last(*vec1)))]
#[ensures(^unwrap(last(*vec1)) == ^unwrap(last(^vec2)))]
fn test<'c, 'a>(vec1: &'c mut Vec<&'a mut u32>, vec2: &'c mut Vec<&'a mut u32>) {
    let x = vec1.pop().unwrap();
    *x += 1;
    vec2.push(x)
}
