use creusot_contracts::*;
use ::std::ops::{Deref, DerefMut};
use crate::head_dst::{new_uninit_box_slice, realloc_box_slice};
use crate::mem::transmute::{ArrTFn, BoxTFn, MutTFn, RefTFn, transmute, TransmuteFn};
use crate::mem::uninit::{AssumeInitTFn, MaybeUninit, MaybeUninitTFn, memcpy};

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
        let data = new_uninit_box_slice(0); // todo replace with Box::new([])
        Vec{len: 0, data}
    }

    #[requires(self.invariant())]
    #[ensures(result.0 == self.len)]
    #[ensures(result.1 == self.data)]
    #[ensures(Vec{len: result.0, data: result.1}.invariant())]
    pub fn into_raw_parts(self) -> (usize, Box<[MaybeUninit<T>]>) {
        let mut me = self;
        let mut dummy = new_uninit_box_slice(0); // todo replace with Box::new([])
        let data = ::std::mem::replace(&mut me.data,dummy);
        (me.len, data)
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
    #[requires((@(*self).len + @new_elems) * 2 <= @usize::MAX)]
    #[ensures((^self).len == (*self).len)]
    #[ensures((^self).data.model().len() >= @(*self).len + @new_elems)]
    #[ensures((^self).data.model().len() >= (*self).data.model().len())]
    #[ensures((^self).data.model().subsequence(0, (*self).data.model().len()) == (*self).data.model())]
    #[ensures((^self).invariant())]
    pub fn reserve(&mut self, new_elems: usize) {
        let mut new_cap = self.data.len();
        let target = self.len + new_elems;
        proof_assert!(@target * 2 <= @usize::MAX);
        while new_cap < target {
            new_cap *= 2
        }
        self.reserve_exact(new_cap)
    }

    #[requires((*self).invariant())]
    #[ensures((^self).len == (*self).len)]
    #[ensures((^self).data.model().len() == @(*self).len)]
    #[ensures((*self).data.model().subsequence(0, (^self).data.model().len()) == (^self).data.model())]
    #[ensures((^self).invariant())]
    pub fn shrink_to_fit(&mut self) {
        let Vec{data, ref len} = self;
        //let old_data: Ghost<Seq<MaybeUninit<T>>> = ghost!(data.model());
        realloc_box_slice(data, *len);
    }

    #[requires((*self).invariant())]
    #[requires(@(*self).len * 2 < @usize::MAX)]
    #[ensures(@(^self).len == @(*self).len + 1)]
    #[ensures((^self).invariant())]
    pub fn push(&mut self, new: T) {
        if self.len == self.data.len() {
            let len = self.len;
            let new_len = if len == 0 { 10 } else { len * 2 };
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

    #[requires((@self.len + (@src).len()) * 2 <= @usize::MAX)]
    #[requires(forall<i: Int> 0 <= i && i < (@*src).len() ==> (@*src)[i].is_init())]
    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[ensures(@(^self).len == @(*self).len + (@src).len())]
    #[ensures(forall<i: Int> 0 <= i && i < (@^src).len() ==>  !(@^src)[i].is_init())]
    pub fn extend_from_maybe_uninit(&mut self, src: &mut [MaybeUninit<T>]) {
        self.reserve(src.len());
        let Vec{data, len} = self;
        let old_len = *len;
        *len += src.len();
        let dst = &mut data[old_len..*len];
        proof_assert!(forall<i: Int> @old_len <= i && i < @len ==> (@^data)[i] == (@^dst)[i - @old_len]);
        memcpy(src, dst);
    }

    #[requires((@self.len + @other.len) * 2 <= @usize::MAX)]
    #[requires(self.invariant())]
    #[requires(other.invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^other).invariant())]
    #[ensures(@(^self).len == @(*self).len +  @(*other).len)]
    #[ensures(@(^other).len == 0)]
    pub fn append(&mut self, other: &mut Self) {
        let src = &mut other.data[0..other.len];
        self.extend_from_maybe_uninit(src);
        proof_assert!(forall<i: Int> 0 <= i && i < (@src).len() ==> (@src)[i] == (@other.data)[i]);
        other.len = 0;
    }

    #[requires(self.invariant())]
    #[ensures((@result).len() == @self.len)]
    pub fn into_box_slice(self) -> Box<[T]> {
        let mut me = self;
        me.shrink_to_fit();
        let data = me.into_raw_parts().1;
        transmute::<_, BoxTFn<ArrTFn<AssumeInitTFn>>>(data)
    }
}

impl<T> Drop for Vec<T> {
    #[requires((*self).invariant())]
    #[requires((^self).invariant())]
    fn drop(&mut self) {
        #[invariant(inv, self.invariant())]
        while self.len > 0 {
            self.pop();
        }
    }
}

impl<T> Deref for Vec<T> {
    type Target = [T];

    #[requires(self.invariant())]
    #[ensures((@result).len() == @self.len)]
    fn deref(&self) -> &Self::Target {
        let init = &self.data[0..self.len];
        transmute::<_, RefTFn<ArrTFn<AssumeInitTFn>>>(init)
    }
}

impl<T> DerefMut for Vec<T> {
    #[requires((*self).invariant())]
    #[ensures((@result).len() == @self.len)]
    #[ensures((^self).len == (*self).len)]
    #[ensures((^self).invariant())]
    fn deref_mut(&mut self) -> &mut Self::Target {
        let init = &mut self.data[0..self.len];
        let res = transmute::<_, MutTFn<ArrTFn<AssumeInitTFn>, ArrTFn<MaybeUninitTFn>>>(init);
        proof_assert!(forall<i: Int> 0 <= i && i < (@^init).len() ==> (@^init)[i].is_init());
        proof_assert!(@(^self).len == (@^init).len());
        proof_assert!(forall<i: Int> 0 <= i && i < @(^self).len ==> (@(^self).data)[i] == (@^init)[i]);
        res
    }
}

impl<T> From<Box<[T]>> for Vec<T> {
    #[ensures(result.invariant())]
    fn from(b: Box<[T]>) -> Self {
        let data = transmute::<_, BoxTFn<ArrTFn<MaybeUninitTFn>>>(b);
        Vec{len: data.len(), data}
    }
}

#[cfg_attr(not(feature = "contracts"), test)]
fn test() {
    let mut x = Vec::new();
    x.push(1);
    x.push(2);
    x.get(1).unwrap();
    assert!(x.get(5).is_none());
    x.pop().unwrap();
    let mut y = Vec::new();
    y.push(1);
    x.append(&mut y);
    assert!(y.pop().is_none());
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