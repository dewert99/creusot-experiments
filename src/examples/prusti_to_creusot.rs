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

#[requires(**x < 100u32)]
#[ensures(**result == **x + 1u32)]
#[ensures(^*result == ^*x)]
//#[ensures(^result == ^x)] // this would imply the next two
#[ensures(*^result == *^x)]
#[ensures(^^result == ^^x)]
fn test2<'o, 'i>(x: &'o mut &'i mut u32) -> &'o mut &'i mut u32 {
    **x += 1;
    x
}