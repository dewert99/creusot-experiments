use creusot_contracts::*;
use crate::ghost_ptr::*;
use crate::p_map::PMap;
use crate::helpers::unwrap;

struct Node<T>{
    data: T,
    next: Ptr<T>,
}

type Ptr<T> = GhostPtr<Node<T>>;
type Token<T> = GhostToken<Node<T>>;
type TokenM<T> = PMap<Ptr<T>, Node<T>>;

#[predicate]
#[variant(token.len())]
#[ensures(ptr == other ==> result)]
#[ensures(token.contains(ptr) && token.lookup(ptr).next == other ==> result)]
fn lseg<T>(ptr: Ptr<T>, other: Ptr<T>, token: TokenM<T>) -> bool {
    if ptr == other {
        true
    } else {
        match token.get(ptr) {
            None => false,
            Some(node) => lseg(node.next, other, token.remove(ptr))
        }
    }
}

#[logic]
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

#[logic]
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

#[predicate]
fn lseg_strict<T>(ptr: Ptr<T>, other: Ptr<T>, token: TokenM<T>) -> bool {
    lseg(ptr, other, token) && lseg_basis(ptr, other, token).ext_eq(token)
}

#[logic]
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

#[logic]
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
fn lseg_trans<T>(ptr1: Ptr<T>, ptr2: Ptr<T>, ptr3: Ptr<T>, token12: TokenM<T>, token23: TokenM<T>) -> bool {
    TokenM::<T>::union_remove;
    if ptr1 != ptr2 {
        let Node{data, next} = token12.lookup(ptr1);
        lseg_trans(next, ptr2, ptr3, token12.remove(ptr1), token23) &&
            token12.union(token23).remove(ptr1) == token12.remove(ptr1).union(token23) &&
            lseg_seq(ptr1, ptr2, token12) ==
                Seq::singleton(data).
                    concat(lseg_seq(next, ptr2, token12.remove(ptr1))) &&
            lseg_seq(ptr1, ptr3, token12.union(token23)) ==
                Seq::singleton(data).
                    concat(lseg_seq(next, ptr3, token12.union(token23).remove(ptr1)))
    } else {
        lseg_super(ptr2, ptr3, token23, token12.union(token23))
    }
}

// #[logic]
// #[requires(len >= 0)]
// #[requires(lseg(ptr, None, len, token) != None)]
// #[ensures(result.len() == len)]
// #[variant(len)]
// fn ptr_to_seq<T>(ptr: OPtr<T>, len: Int, token: TokenM<T>) -> Seq<T> {
//     match ptr {
//         None => Seq::EMPTY,
//         Some(ptr) => {
//             let node = token.lookup(ptr);
//             cons(node.data, ptr_to_seq(node.next, len - 1, token.remove(ptr)))
//         }
//     }
// }



pub struct LinkedList<T>{
    head: Ptr<T>,
    tail: Ptr<T>,
    token: Token<T>,
}

impl<T> LinkedList<T> {

    #[predicate]
    pub fn invariant(self) -> bool {
        let LinkedList{head, tail, token} = self;
        if head == Ptr::null_logic() {
            token.model().is_empty()
        } else {
            lseg_strict(head, tail, token.model().remove(tail)) &&
                token.model().contains(tail) && token.model().lookup(tail).next == Ptr::null_logic()
        }
    }

    #[logic]
    #[requires(self.invariant())]
    pub fn to_seq(self) -> Seq<T> {
        let LinkedList{head, tail, token} = self;
        if head == Ptr::null_logic() {
            Seq::EMPTY
        } else {
            lseg_seq(head, tail, token.model().remove(tail)).push(token.model().lookup(tail).data)
        }
    }

    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn len(self) -> Int {
        self.to_seq().len()
    }

    #[requires((*self).invariant())]
    #[requires(self.head != Ptr::null_logic())]
    #[ensures(result.data == (*self).to_seq().head() && (^self).to_seq().ext_eq((*self).to_seq().tail()))]
    #[ensures((^self).invariant())]
    fn dequeue_box(&mut self) -> Box<Node<T>> {
        let old_self = ghost!(self);
        let LinkedList{head, ref tail, token} = self;
        let old_token: Ghost<TokenM<T>>  = ghost!(token.model());
        let res = head.take_box(token);
        let next = res.next;
        proof_assert!(next != Ptr::null_logic() ==> token.model().remove(*tail).ext_eq(old_token.remove(*tail).remove(*head)));
        *head = next;
        proof_assert!(next == Ptr::null_logic() ==> self.to_seq().ext_eq(old_self.to_seq().tail()));
        proof_assert!(next != Ptr::null_logic() ==> self.to_seq().ext_eq(old_self.to_seq().tail()));
        res
    }

    #[requires((*self).invariant())]
    #[requires(self.head != Ptr::null_logic())]
    #[ensures((^self).to_seq().ext_eq(Seq::singleton(val.data).concat((*self).to_seq())))]
    #[ensures((^self).invariant())]
    fn push_box(&mut self, val: Box<Node<T>>) {
        let old_self: Ghost<&mut Self> = ghost!(self);
        let mut val = val;
        let LinkedList{head, ref tail, token} = self;
        val.next = *head;
        let ptr = GhostPtr::from_box_in(val, token);
        proof_assert!(old_self.token.model().remove(*tail).ext_eq(token.model().remove(*tail).remove(ptr)));
        *head = ptr;
        //proof_assert!(old_self.to_seq() == lseg_seq(old_self.head, *tail, old_self.token.model().remove(*tail)).push(old_self.token.model().lookup(*tail).data));
    }

    #[ensures(result.token.model().len() == 0)]
    #[ensures(result.invariant())]
    pub fn new() -> Self {
        LinkedList{head: Ptr::null(), tail: Ptr::null(), token: Token::new()}
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).to_seq().ext_eq((*self).to_seq().push(elt)))]
    pub fn enqueue(&mut self, elt: T) {
        let old_self = ghost!(self);
        let LinkedList{head, tail, token} = self;
        let old_token: Ghost<TokenM<T>> = ghost!(token.model());
        let node = Node{data: elt, next: Ptr::null()};
        let ptr = GhostPtr::new_in(node, token);
        if head.is_null() {
            *head = ptr;
            *tail = ptr;
            proof_assert!(token.model().remove(*tail) == (lseg_basis(ptr, *tail, token.model())));
        } else {
            let head = &*head;
            proof_assert!(lseg_super(*head, *tail, old_token.remove(*tail), *old_token));
            tail.borrow_mut(token).next = ptr;
            proof_assert!(old_token.remove(*tail).ext_eq(token.model().remove(ptr).remove(*tail)));
            let old_token: Ghost<TokenM<T>> = ghost!(token.model().remove(ptr));
            proof_assert!(lseg_basis(*head, *tail, old_token.remove(*tail)).ext_eq(old_token.remove(*tail)));
            proof_assert!(lseg_trans(*head, *tail, ptr, old_token.remove(*tail), PMap::empty().insert(*tail, old_token.lookup(*tail))));
            proof_assert!(old_token.remove(*tail).union(PMap::empty().insert(*tail, old_token.lookup(*tail))).ext_eq(*old_token));
            proof_assert!(lseg_seq(*head, ptr, *old_token).ext_eq(old_self.to_seq()));
            *tail = ptr;
        }
    }

    #[requires((*self).invariant())]
    #[ensures(self.len() == 0 ==> result == None && *self == ^self)]
    #[ensures(self.len() != 0 ==>
        result == Some((*self).to_seq().head()) && (^self).to_seq().ext_eq((*self).to_seq().tail()))]
    #[ensures((^self).invariant())]
    pub fn dequeue(&mut self) -> Option<T> {
        if self.head.is_null() {
            None
        } else {
            Some(self.dequeue_box().data)
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(forall<i: Int> 0 <= i && i < (^self).len() ==>
        (^self).to_seq()[i] == (*self).to_seq()[(*self).len() - 1 - i])]
    #[ensures((^self).len() == (*self).len())]
    pub fn reverse(&mut self) {
        if self.head.is_null() {
            return
        }
        let old_list = ghost!(self);
        let mut front = self.dequeue_box();
        front.next = Ptr::null();
        let mut new_token = Token::new();
        let ptr = Ptr::from_box_in(front, &mut new_token);
        let mut new_list = LinkedList{head: ptr, tail: ptr, token: new_token};
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
            proof_assert!(self.to_seq().ext_eq(old_list.to_seq().subsequence(new_list.len() + 1, old_list.len())));
            new_list.push_box(b)
        }
        *self = new_list
    }

    #[requires((*self).invariant())]
    #[ensures(result.invariant())]
    #[ensures(result.curr_seq() == (*self).to_seq())]
    #[ensures(result.fut_inv() ==> (^self).invariant() && result.fut_seq() == (^self).to_seq())]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        let token = &mut self.token;
        IterMut { curr: self.head, token, tail: ghost!(self.tail)}
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

pub struct IterMut<'a, T>{
    curr: Ptr<T>,
    token: &'a mut Token<T>,
    tail: Ghost<Ptr<T>>,
}

#[predicate]
fn token_shrink<T>(t: Token<T>, ft: Token<T>) -> bool {
    pearlite!{forall<p: Ptr<T>> (@ft).contains(p) ==> (@t).contains(p)}
}

impl<'a, T> IterMut<'a, T> {

    #[predicate]
    pub fn invariant(self) -> bool {
        LinkedList{head: self.curr, tail: *self.tail, token: *self.token}.invariant()
    }

    #[predicate]
    pub fn produces(self, fut: Self) -> bool {
        pearlite!{fut.fut_inv() ==> self.fut_inv()}
    }

    #[law]
    #[requires(s1.produces(s2) && s2.produces(s3))]
    #[ensures(s1.produces(s3))]
    pub fn produces_trans(s1: Self, s2: Self, s3: Self) {}

    #[logic]
    #[requires(self.invariant())]
    #[ensures(result.len() == self.token.model().len())]
    pub fn curr_seq(self) -> Seq<T> {
        LinkedList{head: self.curr, tail: *self.tail, token: *self.token}.to_seq()
    }

    #[predicate]
    fn fut_inv(self) -> bool {
        pearlite!{LinkedList{head: self.curr, tail: *self.tail, token: ^self.token}.invariant()}
    }

    #[logic]
    #[requires(self.fut_inv())]
    pub fn fut_seq(self) -> Seq<T> {
        pearlite!{LinkedList{head: self.curr, tail: *self.tail, token: ^self.token}.to_seq()}
    }

    #[requires((*self).invariant())]
    #[ensures((*self).curr_seq().len() == 0 ==> result == None && *self == ^self)]
    #[ensures((*self).curr_seq().len() != 0 ==> match result {
        None => false,
        Some(elt) => Seq::singleton(*elt).concat((^self).curr_seq()).ext_eq((*self).curr_seq()) &&
            ((*self).fut_inv() ==> Seq::singleton(^elt).concat((^self).fut_seq()).ext_eq((*self).fut_seq()))
    })]
    #[ensures((^self).fut_inv() ==> (*self).fut_inv())]
    #[ensures((^self).invariant())]
    #[ensures((*self).produces(^self))]
    pub fn next(&mut self) -> Option<&'a mut T> {
        let old_self = ghost!(self);
        let IterMut { curr, token, ..} = self;
        let tail = ghost!(*self.tail);
        if curr.is_null() {
            proof_assert!(self.invariant());
            None
        } else {
            let old_token: Ghost<&mut Token<T>>  = ghost!(*token);
            let old_token_m: Ghost<TokenM<T>>  = ghost!(token.model());
            let Node{data, ref next} = curr.reborrow(token);
            proof_assert!(*next != Ptr::null_logic() ==> token.model().remove(*tail).ext_eq(old_token_m.remove(*tail).remove(*curr)));
            proof_assert!(@^*old_token == (@^*token).insert(*curr, Node{data: ^data, next: *next}));
            proof_assert!((@^*old_token).remove(*curr).ext_eq(@^*token));
            proof_assert!(*curr != *tail ==>
                (@^*token).remove(*tail).ext_eq((@^*old_token).remove(*tail).remove(*curr)));
            //proof_assert!(lseg_strict(*curr, *next, PMap::empty().insert(*curr, Node{data: ^data, next: *next})));
            //proof_assert!(*curr != *tail && lseg(*next, *tail, (@^*token).remove(*tail)) ==> lseg(*curr, *tail, (@^*old_token).remove(*tail)));
            proof_assert!(*curr != *tail && lseg_strict(*next, *tail, (@^*token).remove(*tail))
                ==> lseg_strict(*curr, *tail, (@^*old_token).remove(*tail)));
            *curr = *next;
            proof_assert!(self.fut_inv() ==> old_self.fut_inv());
            proof_assert!(*next != Ptr::null_logic() && old_self.fut_inv() ==>
                Seq::singleton(^data).concat(self.fut_seq()).ext_eq(old_self.fut_seq()));
            proof_assert!(*next != Ptr::null_logic() ==> Seq::singleton(*data).concat(self.curr_seq()).ext_eq(old_self.curr_seq()));
            proof_assert!(*next != Ptr::null_logic() ==> LinkedList{head: *curr, tail: *tail, token: **token}.invariant());
            // proof_assert!((@^*token).subset(@**token) && LinkedList{head: *curr, tail: *tail, token: ^*token}.invariant()
            // ==> LinkedList{head: *head, tail: *tail, token: ^*full_token}.invariant() );
            // proof_assert!(LinkedList{head: *curr, tail: *tail, token: **token}.invariant());
            Some(data)
        }
    }

    #[requires(self.invariant())]
    #[ensures(self.fut_inv())]
    #[ensures(self.curr_seq() == self.fut_seq())]
    pub fn drop(self) {
        let IterMut { curr, token, ..} = self;
    }
}
