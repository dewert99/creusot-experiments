use crate::ghost_ptr::*;
use crate::helpers::unwrap;
use crate::p_map::PMap;
use creusot_contracts::{logic as base_logic, prusti_prelude::*};

pub struct Node<T> {
    pub data: T,
    pub next: Ptr<T>,
}

type Ptr<T> = GhostPtr<Node<T>>;
type Token<T> = GhostToken<Node<T>>;
type TokenM<T> = PMap<Ptr<T>, Node<T>>;

#[predicate('_, '_, '_)]
#[variant(token.len())]
#[ensures(ptr == other ==> result)]
#[ensures(token.contains(ptr) && token.lookup(ptr).next == other ==> result)]
fn lseg<T>(ptr: Ptr<T>, other: Ptr<T>, token: TokenM<T>) -> bool {
    if ptr == other {
        true
    } else {
        match token.get(ptr) {
            None => false,
            Some(node) => lseg(node.next, other, token.remove(ptr)),
        }
    }
}

#[logic(('x, 'x, 'x) -> 'x)]
#[variant(token.len())]
#[requires(lseg(ptr, other, token))]
#[ensures(result.subset(token))]
#[ensures(lseg(ptr, other, result))]
#[ensures(forall<t: TokenM<T>> result.subset(t) ==> lseg(ptr, other, t))]
#[ensures(ptr == other ==> result == PMap::empty())]
fn lseg_basis<T>(ptr: Ptr<T>, other: Ptr<T>, token: TokenM<T>) -> TokenM<T> {
    if ptr == other {
        TokenM::empty()
    } else {
        let node = token.lookup(ptr);
        lseg_basis(node.next, other, token.remove(ptr)).insert(ptr, node)
    }
}

#[logic(('x, 'x, 'x) -> 'x)]
#[variant(token.len())]
#[requires(lseg(ptr, other, token))]
#[ensures(result.len() == lseg_basis(ptr, other, token).len())]
#[ensures(ptr == other ==> result == Seq::EMPTY)]
fn lseg_seq<T>(ptr: Ptr<T>, other: Ptr<T>, token: TokenM<T>) -> Seq<T> {
    if ptr == other {
        Seq::EMPTY
    } else {
        let node = token.lookup(ptr);
        Seq::singleton(node.data).concat(lseg_seq(node.next, other, token.remove(ptr)))
    }
}

#[predicate('_, '_, '_)]
fn lseg_strict<T>(ptr: Ptr<T>, other: Ptr<T>, token: TokenM<T>) -> bool {
    lseg(ptr, other, token) && lseg_basis(ptr, other, token).ext_eq(token)
}

#[logic(('_, '_, '_, '_) -> '_)]
#[variant(token1.len())]
#[requires(lseg(ptr, other, token1))]
#[requires(token1.subset(token2))]
#[ensures(result)]
#[ensures(result ==> lseg(ptr, other, token2))]
#[ensures(result ==> lseg_basis(ptr, other, token1) == lseg_basis(ptr, other, token2))]
#[ensures(result ==> lseg_seq(ptr, other, token1).ext_eq(lseg_seq(ptr, other, token2)))]
fn lseg_super<T>(ptr: Ptr<T>, other: Ptr<T>, token1: TokenM<T>, token2: TokenM<T>) -> bool {
    if ptr != other {
        let next = token1.lookup(ptr).next;
        lseg_super(next, other, token1.remove(ptr), token2.remove(ptr))
    } else {
        true
    }
}

#[logic(('_, '_, '_, '_, '_) -> '_)]
#[variant(token12.len())]
#[requires(token12.disjoint(token23))]
#[requires(lseg(ptr1, ptr2, token12))]
#[requires(lseg(ptr2, ptr3, token23))]
#[requires(!token12.contains(ptr3))]
#[ensures(result)]
#[ensures(result ==> lseg(ptr1, ptr3, token12.union(token23)))]
#[ensures(result ==> lseg_basis(ptr1, ptr3, token12.union(token23)).ext_eq(lseg_basis(ptr1, ptr2, token12).union(lseg_basis(ptr2, ptr3, token23))))]
#[ensures(result ==> lseg_seq(ptr1, ptr3, token12.union(token23)).ext_eq(lseg_seq(ptr1, ptr2, token12).concat(lseg_seq(ptr2, ptr3, token23))))]
// TODO clean up once why3 gets a better discriminate transformation
fn lseg_trans<T>(
    ptr1: Ptr<T>,
    ptr2: Ptr<T>,
    ptr3: Ptr<T>,
    token12: TokenM<T>,
    token23: TokenM<T>,
) -> bool {
    TokenM::<T>::union_remove;
    if ptr1 != ptr2 {
        let Node { data, next } = token12.lookup(ptr1);
        lseg_trans(next, ptr2, ptr3, token12.remove(ptr1), token23)
            && token12.union(token23).remove(ptr1) == token12.remove(ptr1).union(token23)
            && lseg_seq(ptr1, ptr2, token12)
                == Seq::singleton(data).concat(lseg_seq(next, ptr2, token12.remove(ptr1)))
            && lseg_seq(ptr1, ptr3, token12.union(token23))
                == Seq::singleton(data).concat(lseg_seq(
                    next,
                    ptr3,
                    token12.union(token23).remove(ptr1),
                ))
    } else {
        lseg_super(ptr2, ptr3, token23, token12.union(token23))
    }
}

pub struct LinkedList<T> {
    head: Ptr<T>,
    tail: Ptr<T>,
    token: Token<T>,
}

impl<T> LinkedList<T> {
    #[predicate('_)]
    pub fn invariant(self) -> bool {
        let LinkedList { head, tail, token } = self;
        if head == Ptr::null_logic() {
            token.shallow_model().is_empty()
        } else {
            lseg_strict(head, tail, token.shallow_model().remove(tail))
                && token.shallow_model().contains(tail)
                && token.shallow_model().lookup(tail).next == Ptr::null_logic()
        }
    }

    #[logic(('x) -> 'x)]
    #[requires(self.invariant())]
    pub fn to_seq(self) -> Seq<T> {
        let LinkedList { head, tail, token } = self;
        if head == Ptr::null_logic() {
            Seq::EMPTY
        } else {
            lseg_seq(head, tail, token.shallow_model().remove(tail))
                .push(token.shallow_model().lookup(tail).data)
        }
    }

    #[ensures(result.to_seq().ext_eq(Seq::EMPTY))]
    #[ensures(result.invariant())]
    pub fn new() -> Self {
        LinkedList {
            head: Ptr::null(),
            tail: Ptr::null(),
            token: Token::new(),
        }
    }

    #[ensures(result.to_seq().ext_eq(Seq::singleton(b.data)))]
    #[ensures(result.invariant())]
    pub fn from_box(b: Box<Node<T>>) -> Self {
        let mut b = b;
        b.next = Ptr::null();
        let mut token = Token::new();
        let ptr = Ptr::from_box_in(b, &mut token);
        proof_assert!(token.shallow_model().remove(ptr).ext_eq(PMap::empty()));
        LinkedList {
            head: ptr,
            tail: ptr,
            token,
        }
    }

    #[requires(self.invariant())]
    #[ensures(result == (self.to_seq() == Seq::EMPTY))]
    fn empty(&self) -> bool {
        self.head.is_null()
    }

    #[logic(('_) -> '_)]
    #[why3::attr = "inline:trivial"]
    pub fn len(self) -> Int {
        self.to_seq().len()
    }

    #[requires(self.invariant())]
    #[requires(self.head != Ptr::null_logic())]
    #[ensures(result.data == old(self.to_seq().head()) && self.to_seq().ext_eq(old(self.to_seq().tail())))]
    #[ensures(self.invariant())]
    fn dequeue_box(&mut self) -> Box<Node<T>> {
        let old_self = ghost!(self);
        let LinkedList {
            head,
            ref tail,
            token,
        } = self;
        let old_token: Ghost<TokenM<T>> = ghost!(token.shallow_model());
        let res = head.take_box(token);
        let next = res.next;
        proof_assert!(next != Ptr::null_logic() ==> token.shallow_model().remove(*tail).ext_eq(old_token.remove(*tail).remove(*head)));
        *head = next;
        proof_assert!(next == Ptr::null_logic() ==> self.to_seq().ext_eq(old_self.to_seq().tail()));
        proof_assert!(next != Ptr::null_logic() ==> self.to_seq().ext_eq(old_self.to_seq().tail()));
        res
    }

    #[requires(self.invariant())]
    #[requires(self.head != Ptr::null_logic())]
    #[ensures(self.to_seq().ext_eq(Seq::singleton(val.data).concat(old(self.to_seq()))))]
    #[ensures(self.invariant())]
    fn push_box(&mut self, val: Box<Node<T>>) {
        let old_self: Ghost<&mut Self> = ghost!(self);
        let mut val = val;
        let LinkedList {
            head,
            ref tail,
            token,
        } = self;
        val.next = *head;
        let ptr = GhostPtr::from_box_in(val, token);
        proof_assert!(old_self
            .token
            .shallow_model()
            .remove(*tail)
            .ext_eq(token.shallow_model().remove(*tail).remove(ptr)));
        *head = ptr;
    }

    #[requires(self.invariant())]
    #[ensures(self.invariant())]
    #[ensures(self.to_seq().ext_eq(old(self.to_seq()).push(elt)))]
    pub fn enqueue(&mut self, elt: T) {
        let other_list = LinkedList::from_box(Box::new(Node {
            data: elt,
            next: Ptr::null(),
        }));
        let this_list = std::mem::replace(self, other_list);
        let mut iter = self.iter_mut();
        iter.insert_list(this_list);
        iter.drop();
    }

    #[requires(self.invariant())]
    #[ensures(old(self.len()) == 0 ==> result == None && old(*self) == *self)]
    #[ensures(old(self.len()) != 0 ==>
        result == Some(old(self.to_seq()).head()) && self.to_seq().ext_eq(old(self.to_seq()).tail()))]
    #[ensures(self.invariant())]
    pub fn dequeue(&mut self) -> Option<T> {
        if self.head.is_null() {
            None
        } else {
            Some(self.dequeue_box().data)
        }
    }

    #[requires(self.invariant())]
    #[ensures(self.invariant())]
    #[ensures(forall<i: Int> 0 <= i && i < (*self).len() ==>
        self.to_seq()[i] == old(self.to_seq())[(*self).len() - 1 - i])]
    #[ensures(self.len() == old(self.len()))]
    pub fn reverse(&mut self) {
        if self.head.is_null() {
            return;
        }
        let old_list = ghost!(self);
        let mut front = self.dequeue_box();
        front.next = Ptr::null();
        let mut new_token = Token::new();
        let ptr = Ptr::from_box_in(front, &mut new_token);
        let mut new_list = LinkedList {
            head: ptr,
            tail: ptr,
            token: new_token,
        };
        proof_assert!(new_list.len() == 1);
        proof_assert!(new_list.len() == 1);
        #[invariant(old_inv, self.invariant())]
        #[invariant(new_inv, new_list.invariant())]
        #[invariant(non_empty, new_list.head != Ptr::null_logic())]
        #[invariant(fut, ^self == ^*old_list)]
        #[invariant(rev, forall<i: Int> 0 <= i && i < new_list.len() ==>
            new_list.to_seq()[i] == old_list.to_seq()[new_list.len() - 1 - i])]
        #[invariant(size, new_list.len() <= old_list.len())]
        #[invariant(prog, self.to_seq().ext_eq(old_list.to_seq().subsequence(new_list.len(), old_list.len())))]
        while !self.head.is_null() {
            let b = self.dequeue_box();
            proof_assert!(self.to_seq().ext_eq(
                old_list
                    .to_seq()
                    .subsequence(new_list.len() + 1, old_list.len())
            ));
            new_list.push_box(b)
        }
        *self = new_list
    }

    #[requires(self.invariant())]
    #[ensures(result.invariant())]
    #[ensures(result.curr_seq() == old(self.to_seq()))]
    #[after_expiry(result.fut_inv() ==> self.invariant() && result.fut_seq() == self.to_seq())]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        let LinkedList { head, token, tail } = self;
        IterMut {
            curr: head,
            token,
            tail: ghost!(*tail),
        }
    }

    #[requires(self.invariant())]
    pub fn drop(mut self) {
        #[invariant(inv, self.invariant())]
        loop {
            match self.dequeue() {
                None => break,
                _ => continue,
            }
        }
        self.token.drop()
    }

    #[requires(self.invariant())]
    #[requires(other.invariant())]
    #[ensures(self.to_seq().ext_eq(other.to_seq().concat(old(self.to_seq()))))]
    #[ensures(self.invariant())]
    fn prepend(&mut self, other: LinkedList<T>) {
        if self.empty() {
            *self = other
        } else {
            let mut iter = self.iter_mut();
            iter.insert_list(other);
            iter.drop();
        }
    }
}

#[cfg_attr(not(feature = "contracts"), test)]
fn test() {
    let mut l = LinkedList::new();
    l.enqueue(1);
    assert!(l.dequeue().unwrap() == 1);
    assert!(l.dequeue().is_none());
    l.enqueue(2);
    l.enqueue(3);
    l.reverse();
    assert!(l.dequeue().unwrap() == 3);
    assert!(l.dequeue().unwrap() == 2);
    assert!(l.dequeue().is_none());
    l.enqueue(5);
    l.enqueue(8);
    let mut it = l.iter_mut();
    let old_it = ghost!(it);
    let a = it.next().unwrap();
    let b = it.next().unwrap();
    let c = it.next();
    proof_assert!(c == None);
    proof_assert!(@a == 5);
    proof_assert!(@b == 8);
    *a += *b;
    *b += *a;
    it.drop();
    proof_assert!(old_it.fut_inv());
    proof_assert!(l.to_seq()[0] == 13u32);
    proof_assert!(l.to_seq()[1] == 21u32);
    proof_assert!(l.to_seq().len() == 2);
    l.drop();
}

pub struct IterMut<'a, T> {
    curr: &'a mut Ptr<T>,
    token: &'a mut Token<T>,
    tail: Ghost<Ptr<T>>,
}

#[base_logic]
#[creusot::prusti::home_sig = "('_, '_, 'x) -> 'x"]
fn linked_list<T>(head: Ptr<T>, tail: Ptr<T>, token: Token<T>) -> LinkedList<T> {
    LinkedList { head, tail, token }
}

impl<'curr, T> IterMut<'curr, T> {
    #[predicate('x)]
    fn fut_inv<'x>(self) -> bool {
        pearlite! {
            (at_expiry::<'x>(*self.curr) != Ptr::null_logic() ==> *self.curr != Ptr::null_logic()) &&
            LinkedList{head: *self.curr, tail: *self.tail, token: *self.token}.invariant()
        }
    }

    #[logic(('x) -> 'curr)]
    #[requires(self.fut_inv())]
    pub fn fut_seq(self) -> Seq<T> {
        linked_list(*self.curr, *self.tail, *self.token).to_seq()
    }

    #[predicate('_, '_)]
    pub fn produces(self, fut: Self) -> bool {
        pearlite! {fut.fut_inv() ==> self.fut_inv()}
    }

    // #[law('_, '_, '_)]
    // #[requires(s1.produces(s2) && s2.produces(s3))]
    // #[ensures(s1.produces(s3))]
    // pub fn produces_trans(s1: Self, s2: Self, s3: Self) {}
}

impl<'a, T> IterMut<'a, T> {
    #[predicate('curr)]
    pub fn invariant(self) -> bool {
        LinkedList {
            head: *self.curr,
            tail: *self.tail,
            token: *self.token,
        }
        .invariant()
    }

    #[logic(('curr) -> 'curr)]
    #[requires(self.invariant())]
    #[ensures(result.len() == self.token.shallow_model().len())]
    pub fn curr_seq(self) -> Seq<T> {
        linked_list(*self.curr, *self.tail, *self.token).to_seq()
    }

    #[requires(self.invariant())]
    #[ensures(old(self.curr_seq()).len() == 0 ==> result == None && old(*self) == *self)]
    #[after_expiry('a, old(self.curr_seq()).len() != 0 ==> match result {
        None => false,
        Some(elt) => curr(Seq::singleton(*elt).concat(self.curr_seq())).ext_eq(old(self.curr_seq())) &&
            (old(*self).fut_inv() ==> Seq::singleton(*elt).concat(curr(*self).fut_seq()).ext_eq(old(*self).fut_seq()))
    })]
    #[after_expiry('a, curr(*self).fut_inv() ==> old(*self).fut_inv())]
    #[ensures(self.invariant())]
    #[after_expiry('a, old(*self).produces(curr(*self)))]
    pub fn next(&mut self) -> Option<&'a mut T> {
        let old_self = ghost!(self);
        let IterMut { curr, token, .. } = self;
        let tail = ghost!(*self.tail);
        if curr.is_null() {
            proof_assert!(self.invariant());
            None
        } else {
            let old_token: Ghost<&mut Token<T>> = ghost!(*token);
            let old_token_m: Ghost<TokenM<T>> = ghost!(token.shallow_model());
            let Node { data, next } = curr.reborrow(token);
            proof_assert!(*next != Ptr::null_logic() ==> token.shallow_model().remove(*tail).ext_eq(old_token_m.remove(*tail).remove(**curr)));
            proof_assert!(@^*old_token == (@^*token).insert(**curr, Node{data: ^data, next: ^next}));
            proof_assert!((@^*old_token).remove(**curr).ext_eq(@^*token));
            proof_assert!(**curr != *tail ==>
                (@^*token).remove(*tail).ext_eq((@^*old_token).remove(*tail).remove(**curr)));
            proof_assert!(**curr != *tail && lseg_strict(^next, *tail, (@^*token).remove(*tail))
                ==> lseg_strict(**curr, *tail, (@^*old_token).remove(*tail)));
            *curr = next;
            proof_assert!(self.fut_inv() ==> old_self.fut_inv());
            proof_assert!(**curr != Ptr::null_logic() && old_self.fut_inv() ==>
                Seq::singleton(^data).concat(self.fut_seq()).ext_eq(old_self.fut_seq()));
            proof_assert!(**curr != Ptr::null_logic() ==> Seq::singleton(*data).concat(self.curr_seq()).ext_eq(old_self.curr_seq()));
            proof_assert!(**curr != Ptr::null_logic() ==> LinkedList{head: **curr, tail: *tail, token: **token}.invariant());
            Some(data)
        }
    }

    #[requires(self.invariant())]
    #[requires(list.invariant())]
    #[requires(self.curr_seq().len() > 0)]
    #[ensures(self.invariant())]
    #[ensures(self.curr_seq().ext_eq(list.to_seq().concat(old(self.curr_seq()))))]
    #[after_expiry('a, old(*self).produces(curr(*self)))]
    #[after_expiry('a, old(*self).fut_inv() ==> curr(*self).fut_seq().ext_eq(old(*self).fut_seq()))]
    pub fn insert_list(&mut self, list: LinkedList<T>) {
        TokenM::<T>::union_remove;
        if list.head.is_null() {
            return;
        }
        let IterMut { curr, token, .. } = self;
        let tail = ghost!(*self.tail);
        let old_list = ghost!(list);
        let LinkedList {
            head: l_head,
            tail: l_tail,
            token: mut l_token,
        } = list;
        let old_l_token = ghost!(l_token);
        let l_tail_node = l_tail.borrow_mut(&mut l_token);
        l_tail_node.next = **curr;
        let l_tail_node = ghost!(*l_tail_node);
        let good = ghost!(old_l_token.shallow_model().disjoint(token.shallow_model()));
        //proof_assert!(l_head != l_tail);
        proof_assert!(*good ==> lseg_strict(l_tail, **curr, PMap::empty().insert(l_tail, *l_tail_node)));
        proof_assert!(*good ==> lseg_seq(l_tail, **curr, PMap::empty().insert(l_tail, *l_tail_node)).ext_eq(Seq::singleton(l_tail_node.data)));
        //proof_assert!(lseg_strict(l_head, l_tail, old_l_token.shallow_model().remove(l_tail)));
        proof_assert!(old_l_token
            .shallow_model()
            .remove(l_tail)
            .disjoint(PMap::empty().insert(l_tail, *l_tail_node)));
        proof_assert!(*good ==> lseg_trans(l_head, l_tail, **curr, old_l_token.shallow_model().remove(l_tail), PMap::empty().insert(l_tail, *l_tail_node)));
        proof_assert!(old_l_token
            .shallow_model()
            .remove(l_tail)
            .union(PMap::empty().insert(l_tail, *l_tail_node))
            .ext_eq(l_token.shallow_model()));
        proof_assert!(*good ==> lseg_seq(l_head, **curr, l_token.shallow_model()).ext_eq(old_list.to_seq()));
        proof_assert!(*good ==> lseg_trans(l_head, **curr, *tail, l_token.shallow_model(), token.shallow_model().remove(*tail)));
        proof_assert!(*good ==> l_token.shallow_model().union(token.shallow_model().remove(*tail)).ext_eq(token.shallow_model().union(l_token.shallow_model()).remove(*tail)));
        //proof_assert!(*good ==> lseg_strict(l_head, *tail, token.shallow_model().union(l_token.shallow_model()).remove(*tail)));
        **curr = l_head;
        token.absorb(l_token);
    }

    #[requires(self.invariant())]
    #[requires(self.curr_seq().len() > 1)]
    #[ensures(self.invariant())]
    #[ensures(self.curr_seq().ext_eq(old(self.curr_seq().tail())))]
    #[after_expiry('a, old(*self).produces(curr(*self)))]
    #[after_expiry('a, old(*self).fut_inv() ==> curr(*self).fut_seq().ext_eq(old(*self).fut_seq()))]
    pub fn remove_box(&mut self) -> Box<Node<T>> {
        TokenM::<T>::union_remove;
        let IterMut { curr, token, .. } = self;
        let tail = ghost!(*self.tail);
        let old_token: Ghost<TokenM<T>> = ghost!(token.shallow_model());
        let res = curr.take_box(token);
        let next = res.next;
        proof_assert!(next != Ptr::null_logic());
        proof_assert!(token
            .shallow_model()
            .remove(*tail)
            .ext_eq(old_token.remove(*tail).remove(**curr)));
        **curr = next;
        res
    }

    #[requires(self.invariant())]
    #[ensures(result.invariant())]
    #[after_expiry(result.fut_inv() ==> self.invariant() && result.fut_seq() == self.curr_seq())]
    #[after_expiry('a, old(*self).produces(at_expiry::<'_>(*self)))]
    #[after_expiry('a, old(*self).fut_inv() ==> at_expiry::<'_>(*self).fut_seq().ext_eq(old(*self).fut_seq()))]
    pub fn reborrow(&mut self) -> IterMut<'_, T> {
        IterMut {
            curr: &mut *self.curr,
            token: &mut *self.token,
            tail: ghost!(*self.tail),
        }
    }

    #[requires(self.invariant())]
    #[after_expiry('a, self.fut_inv())]
    #[after_expiry('a, old(self.curr_seq()) == self.fut_seq())]
    pub fn drop(self) {
        let IterMut { curr, token, .. } = self;
    }
}
