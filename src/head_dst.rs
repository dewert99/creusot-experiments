use creusot_contracts::*;
use ::std::alloc::{alloc, dealloc, handle_alloc_error, Layout, LayoutError, realloc};
use ::std::ptr::{addr_of_mut, from_raw_parts_mut, invalid_mut, NonNull, Pointee, read, write};
use crate::mem::transmute::{BoxTFn, MutTFn, transmute, TransmuteFn};
use crate::mem::uninit::MaybeUninit;

#[repr(C)]
pub struct HeadDst<H, T: ?Sized>{
    pub head: H,
    pub tail: T
}

#[trusted]
unsafe fn zero_alloc(l: Layout) -> *mut u8 {
    if l.size() == 0 {
        invalid_mut(l.align())
    } else {
        alloc(l)
    }
}

#[trusted]
unsafe fn zero_realloc(old: *mut u8, old_layout: Layout, new_size: usize) -> *mut u8 {
    if new_size == 0 {
        if old_layout.size() != 0 {
            dealloc(old, old_layout)
        }
        invalid_mut(old_layout.align())
    } else {
        if old_layout.size() == 0 {
            alloc(Layout::from_size_align_unchecked(new_size, old_layout.align()))
        } else {
            realloc(old, old_layout, new_size)
        }
    }
}

impl<H, E> HeadDst<H, [MaybeUninit<E>]> {

    // Layout for Self with `len`
    #[trusted]
    fn layout(len: usize) -> Result<Layout, LayoutError> {
        let layout_h = Layout::new::<H>();
        let layout_t = Layout::array::<MaybeUninit<E>>(len)?;
        let layout_f = layout_h.extend(layout_t)?.0;
        Ok(layout_f.pad_to_align())
    }


    #[trusted]
    #[ensures((@result.tail).len() == @len)]
    #[ensures(forall<i: Int> 0 <= i && i < @len ==> !(@result.tail)[i].is_init())]
    #[ensures(result.head == head)]
    pub fn new_box(head: H, len: usize) -> Box<Self> {
        unsafe {
            let layout = Self::layout(len).unwrap();
            let r_ptr = zero_alloc(layout);
            if r_ptr.is_null() {
                handle_alloc_error(layout)
            }
            let s_ptr: *mut HeadDst<H, [MaybeUninit<E>]> = from_raw_parts_mut(r_ptr as *mut _, len);
            (s_ptr as *mut H).write(head);
            Box::from_raw(s_ptr)
        }
    }

    #[trusted]
    #[ensures((@(^s).tail).len() == @new_len)]
    #[ensures((*s).head == (^s).head)]
    #[ensures(@new_len <= (@(*s).tail).len() ==> @(^s).tail == (@(*s).tail).subsequence(0, @new_len))]
    #[ensures(@new_len >= (@(*s).tail).len() ==> (@(^s).tail).subsequence(0, (@(*s).tail).len()) == @(*s).tail)]
    #[ensures(forall<i: Int> (@(*s).tail).len() <= i && i < @new_len ==> !(@(^s).tail)[i].is_init())]
    fn realloc(s: &mut Box<Self>, new_len: usize) {
        unsafe {
            let old_len = s.tail.len();
            let old_ptr = Box::into_raw(read(s));
            let old_layout = Self::layout(old_len).unwrap();
            let new_layout = Self::layout(new_len).unwrap();
            let new_ptr = zero_realloc(old_ptr as *mut u8, old_layout, new_layout.size());
            if new_ptr.is_null() {
                handle_alloc_error(new_layout)
            }
            let s_ptr: *mut HeadDst<H, [MaybeUninit<E>]> = from_raw_parts_mut(new_ptr as *mut _, new_len);
            write(s, Box::from_raw(s_ptr))
        }
    }
}

pub struct HeadDstEraseTFn;
// Safety HeadDst<(), T> has #[repr(C)] so it has the same layout as T
// Safety (DST) since HeadDst<(), T> last field has type T it has T's metadata
unsafe impl<T: ?Sized> TransmuteFn<HeadDst<(), T>> for HeadDstEraseTFn {
    type Output = T;

    #[predicate]
    fn precondition(self, arg: HeadDst<(), T>) -> bool {
        true
    }

    #[predicate]
    fn postcondition(self, arg: HeadDst<(), T>, res: Self::Output) -> bool {
        arg.tail == res
    }
}

pub struct HeadDstCreateTFn;

// Safety HeadDst<(), T> has #[repr(C)] so it has the same layout as T
// Safety (DST) since HeadDst<(), T> last field has type T it has T's metadata
unsafe impl<T: ?Sized> TransmuteFn<T> for HeadDstCreateTFn {
    type Output = HeadDst<(), T>;

    #[predicate]
    fn precondition(self, arg: T) -> bool {
        true
    }

    #[predicate]
    fn postcondition(self, arg: T, res: Self::Output) -> bool {
        arg == res.tail
    }
}

pub struct HeadDstMapTFn<H, T>(H, T);

// Safety HeadDst has #[repr(C)] and T0/T1 make sure it's safe to transmute it's children
unsafe impl<H, T: ?Sized, HT: TransmuteFn<H>, TT: TransmuteFn<T>> TransmuteFn<HeadDst<H, T>> for HeadDstMapTFn<HT, TT>
    where HT::Output: Sized {
    type Output = HeadDst<HT::Output, TT::Output>;

    #[predicate]
    fn precondition(self, arg: HeadDst<H, T>) -> bool {
        self.0.precondition(arg.head) && self.1.precondition(arg.tail)
    }

    #[predicate]
    #[requires(self.precondition(arg))]
    fn postcondition(self, arg: HeadDst<H, T>, res: Self::Output) -> bool {
        self.0.postcondition(arg.head, res.head) && self.1.postcondition(arg.tail, res.tail)
    }
}

#[ensures((@result).len() == @len)]
#[ensures(forall<i: Int> 0 <= i && i < @len ==> !(@result)[i].is_init())]
pub fn new_uninit_box_slice<T>(len: usize) -> Box<[MaybeUninit<T>]> {
    let hdst = HeadDst::new_box((), len);
    transmute(BoxTFn(HeadDstEraseTFn),hdst)
}

#[ensures((@^b).len() == @new_len)]
#[ensures(@new_len <= (@*b).len() ==> @^b == (@*b).subsequence(0, @new_len))]
#[ensures(@new_len >= (@*b).len() ==> (@^b).subsequence(0, (@*b).len()) == @*b)]
#[ensures(forall<i: Int> (@*b).len() <= i && i < @new_len ==> !(@^b)[i].is_init())]
pub fn realloc_box_slice<T>(b: &mut Box<[MaybeUninit<T>]>, new_len: usize) {
    let hdts_old = transmute(MutTFn(BoxTFn(HeadDstCreateTFn), BoxTFn(HeadDstEraseTFn)), b);
    HeadDst::realloc(hdts_old, new_len);
}