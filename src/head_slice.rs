use creusot_contracts::*;
use ::std::alloc::{alloc, Layout};
use ::std::ptr::{addr_of_mut, from_raw_parts_mut};
use crate::uninit::MaybeUninit;

#[repr(C)]
struct HeadSlice<E, H>{
    head: H,
    tail: [MaybeUninit<E>]
}

impl<E, H> HeadSlice<E, H> {
    #[trusted]
    #[ensures((@result.tail).len() == @len)]
    #[ensures(forall<i: Int> 0 <= i && i < @len ==> !(@result.tail)[i].is_init())]
    #[ensures(result.head == head)]
    pub fn box_new<T>(head: H, len: usize) -> Box<HeadSlice<E, H>> {
        unsafe {
            let layout_h = Layout::new::<H>();
            let layout_t = Layout::array::<MaybeUninit<E>>(len).unwrap();
            let layout_f = layout_h.extend(layout_t).unwrap().0;
            let r_ptr = alloc(layout_f.pad_to_align());
            let s_ptr: *mut HeadSlice<E, H> = from_raw_parts_mut(r_ptr as *mut _, len);
            addr_of_mut!((*s_ptr).head).write(head);
            Box::from_raw(s_ptr)
        }
    }
}