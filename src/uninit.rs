extern crate creusot_contracts;
use creusot_contracts::*;
use ::std::mem;
use ::std::alloc::{alloc, Layout};
use ::std::ptr::slice_from_raw_parts_mut;
use crate::transmute::*;

#[trusted]
pub struct MaybeUninit<T>(mem::MaybeUninit<T>);

pub struct MaybeUninitTFn;

unsafe impl<T> TransmuteFn<T> for MaybeUninitTFn {
    type Output = MaybeUninit<T>;

    #[predicate]
    fn precondition(arg: T) -> bool {
        true
    }

    #[predicate]
    fn postcondition(arg: T, res: Self::Output) -> bool {
        res.model() == Some(arg)
    }
}

pub struct AssumeInitTFn;

unsafe impl<T> TransmuteFn<MaybeUninit<T>> for AssumeInitTFn {
    type Output = T;

    #[predicate]
    fn precondition(arg: MaybeUninit<T>) -> bool {
        arg.is_init()
    }

    #[predicate]
    fn postcondition(arg: MaybeUninit<T>, res: Self::Output) -> bool {
        arg.model() == Some(res)
    }
}




impl<T> Model for MaybeUninit<T> {
    type ModelTy = Option<T>;

    #[trusted]
    #[logic]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}

impl<T> MaybeUninit<T> {

    #[predicate]
    pub fn is_init(&self) -> bool {
        self.model() != None
    }

    #[ensures(@result == Some(t))]
    pub fn new(t: T) -> Self {
        transmute::<_, MaybeUninitTFn>(t)
    }

    #[trusted]
    #[ensures(result == Self::uninit_logic())]
    pub fn uninit() -> Self {
        MaybeUninit(mem::MaybeUninit::uninit())
    }

    #[trusted]
    #[logic]
    #[ensures(@result == None)]
    pub fn uninit_logic() -> Self {
        absurd
    }

    #[requires(self.is_init())]
    #[ensures(Some(result) == @self)]
    pub fn assume_init(self) -> T {
        transmute::<_, AssumeInitTFn>(self)
    }

    #[requires(self.is_init())]
    #[ensures(Some(*result) == @self)]
    pub fn assume_init_ref(&self) -> &T {
        transmute::<_, RefTFn<AssumeInitTFn>>(self)
    }

    #[requires(self.is_init())]
    #[ensures(Some(*result) == @*self && Some(^result) == @^self)]
    pub fn assume_init_mut(&mut self) -> &mut T {
        transmute::<_, MutTFn<AssumeInitTFn, MaybeUninitTFn>>(self)
    }

    #[requires((*self).is_init())]
    #[ensures(!(^self).is_init() && Some(result) == @*self)]
    pub fn take(&mut self) -> T {
        mem::replace(self, Self::uninit()).assume_init()
    }

    #[requires(!(*self).is_init())]
    #[ensures(@^self == Some(t))]
    pub fn write(&mut self, t: T) {
        #[allow(unused_must_use)]
        mem::replace(self, Self::new(t));
    }
}

#[trusted]
#[requires((@src).len() == (@dst).len())]
#[requires(forall<i: Int> 0 <= i && i < (@dst).len() ==> !(@dst)[i].is_init())]
#[ensures(@^src == @*dst)]
#[ensures(@^dst == @*src)]
pub fn memcpy<T>(src: &mut [MaybeUninit<T>], dst: &mut [MaybeUninit<T>]) {
    let count = src.len();
    let src = src as *const _ as *const T;
    let dst = dst as *mut _ as *mut T;
    unsafe {::std::ptr::copy_nonoverlapping(src, dst, count)}
}