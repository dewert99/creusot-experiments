use creusot_contracts::*;
use crate::head_dst::{new_uninit_box_slice, realloc_box_slice};
use crate::uninit::MaybeUninit;

struct Vec<T>{
    len: usize,
    data: Box<[MaybeUninit<T>]>
}

impl<T> Vec<T> {
    #[predicate]
    pub fn invariant(self) -> bool {
        let len = self.len.model();
        let data = self.data.model();
        len <= data.len() && pearlite!{
            (forall<i: Int> 0 <= i && i < len ==> data[i].is_init()) &&
            (forall<i: Int> len <= i && i < data.len() ==> !data[i].is_init())
        }
    }

    #[ensures(result.invariant())]
    #[ensures(@result.len == 0)]
    pub fn with_capacity(len: usize) -> Self {
        Vec{len: 0, data: new_uninit_box_slice(len)}
    }

    #[ensures(result.invariant())]
    #[ensures(@result.len == 0)]
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    #[requires((*self).invariant())]
    #[ensures((^self).len == (*self).len)]
    #[ensures((^self).data.model().len() >= @new_cap)]
    #[ensures((^self).data.model().len() >= (*self).data.model().len())]
    #[ensures((^self).data.model().subsequence(0, (*self).data.model().len()) == (*self).data.model())]
    #[ensures((^self).invariant())]
    pub fn reserve_exact(&mut self, new_cap: usize) {
        let Vec{data, ref len} = self;
        let old_data: Ghost<Seq<MaybeUninit<T>>> = ghost!(data.model());
        if data.len() < new_cap {
            realloc_box_slice(data, new_cap);
        } else {
            proof_assert!((@data).ext_eq((@data).subsequence(0, (@(*self).data).len())))
        }
        proof_assert!(forall<i: Int> 0 <= i && i < @len ==> (@data)[i] == old_data[i] && (@data)[i].is_init());
        proof_assert!(forall<i: Int> @len <= i && i < old_data.len() ==> (@data)[i] == old_data[i]);
        proof_assert!(forall<i: Int> @len <= i && i < old_data.len() ==> !(@data)[i].is_init());
        proof_assert!(forall<i: Int> @len <= i && i < (@data).len() ==> !(@data)[i].is_init());
    }

    #[requires((*self).invariant())]
    #[requires(@(*self).len * 2 < @usize::MAX)]
    #[ensures(@(^self).len == @(*self).len + 1)]
    #[ensures((^self).invariant())]
    pub fn push(&mut self, new: T) {
        if self.len == self.data.len() {
            let len = self.len;
            let new_len = if len == 0 {
                10
            } else {
                len * 2
            };
            self.reserve_exact(new_len);
        }
        let Vec{data, len} = self;
        data[*len].write(new);
        *len += 1;
    }

    #[requires((*self).invariant())]
    #[ensures(@(*self).len > 0 ==> result != None && @(^self).len == @(*self).len - 1)]
    #[ensures(@(*self).len == 0 ==> result == None && ^self == *self)]
    #[ensures((^self).invariant())]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            Some(self.data[self.len].take())
        }
    }
}

#[cfg_attr(not(feature = "contracts"), test)]
fn test() {
    let mut x = Vec::new();
    x.push(1);
    x.push(2);
    x.pop().unwrap();
    x.pop().unwrap();
    assert!(x.pop().is_none());
    x = Vec::with_capacity(1);
    x.push(1);
    x.push(2);
    x.pop().unwrap();
    x.pop().unwrap();
    assert!(x.pop().is_none());
}