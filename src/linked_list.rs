use creusot_contracts::*;
use crate::ghost_ptr::*;
use crate::p_map::PMap;

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
fn lseg_trans<T>(ptr1: Ptr<T>, ptr2: Ptr<T>, ptr3: Ptr<T>, token12: TokenM<T>, token23: TokenM<T>) -> bool {
    TokenM::<T>::union_remove;
    if ptr1 != ptr2 {
        let next = token12.lookup(ptr1).next;
        lseg_trans(next, ptr2, ptr3, token12.remove(ptr1), token23)
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


    #[predicate]
    #[requires(self.invariant())]
    #[ensures(result)]
    #[ensures(result ==> lseg_strict(self.head, Ptr::null_logic(), self.token.model()))]
    pub fn invariant2(self) -> bool {
        let LinkedList{head, tail, token} = self;
        if head == Ptr::null_logic() {
            true
        } else {
            lseg_strict(tail, Ptr::null_logic(), TokenM::empty().insert(tail, token.model().lookup(tail))) &&
                lseg_trans(head, tail, Ptr::null_logic(),
                       token.model().remove(tail), TokenM::empty().insert(tail, token.model().lookup(tail))) &&
                token.model().remove(tail).union(TokenM::empty().insert(tail, token.model().lookup(tail))).ext_eq(token.model())
        }
    }

    #[ensures(result.token.model().len() == 0)]
    #[ensures(result.invariant())]
    pub fn new() -> Self {
        LinkedList{head: Ptr::null(), tail: Ptr::null(), token: Token::new()}
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).token.model().len() == (*self).token.model().len() + 1)]
    pub fn enqueue(&mut self, elt: T) {
        let LinkedList{head, tail, token} = self;
        let old_token: Ghost<TokenM<T>> = ghost!(token.model());
        let node = Node{data: elt, next: Ptr::null()};
        //let gnode: Ghost<Node<T>> = ghost!(node);
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
            *tail = ptr;
        }
    }

    #[requires((*self).invariant())]
    #[ensures(self.token.model().len() == 0 ==> result == None && *self == ^self)]
    #[ensures(self.token.model().len() != 0 ==> result != None && (^self).token.model().len() == (*self).token.model().len() - 1)]
    #[ensures((^self).invariant())]
    pub fn dequeue(&mut self) -> Option<T> {
        let LinkedList{head, ref tail, token} = self;
        if head.is_null() {
            None
        } else {
            let old_token: Ghost<TokenM<T>>  = ghost!(token.model());
            let Node{data, next} = head.take(token);
            proof_assert!(next != Ptr::null_logic() ==> token.model().remove(*tail).ext_eq(old_token.remove(*tail).remove(*head)));
            *head = next;
            Some(data)
        }
    }

    #[requires((*self).invariant())]
    #[ensures(result.invariant())]
    #[ensures(^self == LinkedList{head: *result.head, tail: *result.tail, token: ^*result.full_token})]
    pub fn iter_mut(&mut self) -> IterMut2<'_, T> {
        let token = &mut self.token;
        IterMut2 { curr: self.head, token, head: ghost!(self.head), tail: ghost!(self.tail), full_token: ghost!(token)}
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

// pub struct IterMut<'a, T>{
//     head: Ptr<T>,
//     token: &'a mut Token<T>,
// }
//
// impl<'a, T> IterMut<'a, T> {
//
//     #[predicate]
//     pub fn invariant(self) -> bool {
//         lseg_strict(self.head, Ptr::null_logic(), self.token.model())
//     }
//
//     #[requires((*self).invariant())]
//     #[ensures((*self).token.model().len() == 0 ==> result == None && *self == ^self)]
//     #[ensures((*self).token.model().len() != 0 ==> (^self).token.model().len() == (*self).token.model().len() - 1)]
//     #[ensures((*self).token.model().len() != 0 ==> result != None && (^self).token.model().len() == (*self).token.model().len() - 1)]
//     #[ensures((^self).invariant())]
//     pub fn next(&mut self) -> Option<&'a mut T> {
//         let IterMut{head, token} = self;
//         if head.is_null() {
//             None
//         } else {
//             let old_head: Ghost<Ptr<T>> = ghost!(*head);
//             let old_token: Ghost<TokenM<T>>  = ghost!(token.model());
//             let Node{data, next} = head.reborrow(token);
//             *head = *next;
//             Some(data)
//         }
//     }
// }

#[cfg_attr(not(feature = "contracts"), test)]
fn test() {
    let mut l = LinkedList::new();
    l.enqueue(5);
    l.dequeue();
    l.dequeue();
    l.enqueue(7);
    l.enqueue(9);
    let mut it = l.iter_mut();
    it.next();
    it.next();
    it.next();
    it.drop();
    l.drop();
}

pub struct IterMut2<'a, T>{
    curr: Ptr<T>,
    token: &'a mut Token<T>,
    head: Ghost<Ptr<T>>,
    tail: Ghost<Ptr<T>>,
    full_token: Ghost<&'a mut Token<T>>
}

#[predicate]
fn token_shrink<T>(t: Token<T>, ft: Token<T>) -> bool {
    pearlite!{forall<p: Ptr<T>> (@ft).contains(p) ==> (@t).contains(p)}
}

impl<'a, T> IterMut2<'a, T> {

    #[predicate]
    pub fn invariant(self) -> bool {
        LinkedList{head: self.curr, tail: *self.tail, token: *self.token}.invariant() && pearlite!{
            (self.curr != Ptr::null_logic() ==> *self.head != Ptr::null_logic()) &&
            (token_shrink(*self.token, ^self.token) && LinkedList{head: self.curr, tail: *self.tail, token: ^self.token}.invariant()
            ==> LinkedList{head: *self.head, tail: *self.tail, token: ^*self.full_token}.invariant()) }
    }

    #[predicate]
    pub fn produces(self, fut: Self) -> bool {
        self.head == fut.head && self.tail == fut.tail && self.full_token == fut.full_token
    }

    #[requires((*self).invariant())]
    #[ensures((*self).token.model().len() == 0 ==> result == None && *self == ^self)]
    #[ensures((*self).token.model().len() != 0 ==> (^self).token.model().len() == (*self).token.model().len() - 1)]
    #[ensures((*self).token.model().len() != 0 ==> result != None && (^self).token.model().len() == (*self).token.model().len() - 1)]
    #[ensures((^self).invariant())]
    #[ensures((*self).produces(^self))]
    pub fn next(&mut self) -> Option<&'a mut T> {
        let IterMut2 { curr, token, ..} = self;
        let tail = ghost!(*self.tail);
        let head = ghost!(*self.head);
        let full_token = ghost!(*self.full_token);
        if curr.is_null() {
            proof_assert!(self.invariant());
            None
        } else {
            proof_assert!(*head != Ptr::null_logic());
            let old_token: Ghost<&mut Token<T>>  = ghost!(*token);
            let old_token_m: Ghost<TokenM<T>>  = ghost!(token.model());
            let Node{data, ref next} = curr.reborrow(token);
            proof_assert!(*next != Ptr::null_logic() ==> token.model().remove(*tail).ext_eq(old_token_m.remove(*tail).remove(*curr)));
            proof_assert!(@^*old_token == (@^*token).insert(*curr, Node{data: ^data, next: *next}));
            proof_assert!(token_shrink(**token, ^*token) ==> token_shrink(**old_token, ^*old_token));
            proof_assert!(token_shrink(**token, ^*token) && *curr != *tail ==>
                (@^*token).remove(*tail).ext_eq((@^*old_token).remove(*tail).remove(*curr)));
            //proof_assert!(lseg_strict(*curr, *next, PMap::empty().insert(*curr, Node{data: ^data, next: *next})));
            //proof_assert!(*curr != *tail && lseg(*next, *tail, (@^*token).remove(*tail)) ==> lseg(*curr, *tail, (@^*old_token).remove(*tail)));
            proof_assert!(token_shrink(**token, ^*token) && *curr != *tail && lseg_strict(*next, *tail, (@^*token).remove(*tail))
                ==> lseg_strict(*curr, *tail, (@^*old_token).remove(*tail)));
            proof_assert!(token_shrink(**token, ^*token) && LinkedList{head: *next, tail: *tail, token: ^*token}.invariant()
            ==> LinkedList{head: *curr, tail: *tail, token: ^*old_token}.invariant() );
            *curr = *next;
            proof_assert!(*next != Ptr::null_logic() ==> LinkedList{head: *curr, tail: *tail, token: **token}.invariant());
            // proof_assert!((@^*token).subset(@**token) && LinkedList{head: *curr, tail: *tail, token: ^*token}.invariant()
            // ==> LinkedList{head: *head, tail: *tail, token: ^*full_token}.invariant() );
            // proof_assert!(LinkedList{head: *curr, tail: *tail, token: **token}.invariant());
            Some(data)
        }
    }

    #[requires(self.invariant())]
    #[ensures(LinkedList{head: *self.head, tail: *self.tail, token: ^*self.full_token}.invariant())]
    pub fn drop(self) {
        let IterMut2 { curr, token, ..} = self;
    }
}
