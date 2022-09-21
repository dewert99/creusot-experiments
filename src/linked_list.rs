use creusot_contracts::*;
use crate::ghost_ptr::*;
use crate::p_map::PMap;
use crate::helpers::unwrap;
use crate::mem::invariant_transmute::*;
use crate::mem::drop_guard::*;

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
    #[ensures((^self).invariant())]
    #[ensures(result.fut_seq() == (^self).to_seq())]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        InvToken::<T>::inv_final_lemma;
        let token_inner = &mut self.token;
        let inv = ghost!(TokenInv{curr: self.head, tail: self.tail});
        let token = guard_inv(inv, token_inner);
        IterMut { curr: self.head, token}
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
    proof_assert!(l.to_seq()[0] == 13u32);
    proof_assert!(l.to_seq()[1] == 21u32);
    proof_assert!(l.to_seq().len() == 2);
    l.drop();
}

struct TokenInv<T> {
    curr: Ptr<T>,
    tail: Ptr<T>,
}

impl<T> Inv<Token<T>> for TokenInv<T> {
    #[predicate]
    fn invariant(self, target: Token<T>) -> bool {
        LinkedList{head: self.curr, tail: self.tail, token: target}.invariant()
    }
}

type InvToken<T> = InvGuard<TokenInv<T>, Token<T>>;

pub struct IterMut<'a, T>{
    curr: Ptr<T>,
    token: &'a mut InvToken<T>,
}

#[logic]
fn inv_token_seq<T>(t: InvToken<T>) -> Seq<T> {
    LinkedList{head: t.inv().curr, tail: t.inv().tail, token: t.data}.to_seq()
}

#[requires(curr != Ptr::null_logic())]
#[requires(old_token.inv().curr == curr)]
#[ensures(Seq::singleton(*result.1).concat(inv_token_seq(*result.0)).ext_eq(inv_token_seq(*old_token)))]
#[ensures(Seq::singleton(^result.1).concat(inv_token_seq(^result.0)).ext_eq(inv_token_seq(^old_token)))]
#[ensures(result.2 == (*result.0).inv().curr)]
fn step_token<T>(old_token: &mut InvToken<T>, curr: Ptr<T>) -> (&mut InvToken<T>, &mut T, Ptr<T>) {
    InvToken::<T>::inv_final_lemma;
    let old_token_inner = &mut old_token.data;
    let old_token_inner_g = ghost!(old_token_inner);
    let old_inv = ghost!(old_token.inv());
    let tail = ghost!(old_inv.tail);
    proof_assert!(old_token.inv().invariant(*old_token_inner)); // Manually assume we have the invariant
    let (Node{ref next, data}, token_inner) = curr.reborrow2(old_token_inner);
    let inv = ghost!(TokenInv{curr: *next, tail: *tail});
    proof_assert!(curr != *tail ==> (@*token_inner).remove(*tail).ext_eq((@**old_token_inner_g).remove(*tail).remove(curr)));
    proof_assert!(curr != *tail ==> (@^token_inner).remove(*tail).ext_eq((@^*old_token_inner_g).remove(*tail).remove(curr)));
    proof_assert!(curr != *tail ==> (@^token_inner).ext_eq((@^*old_token_inner_g).remove(curr)));
    let token_inner_g = ghost!(token_inner);
    let token = guard_inv(inv, token_inner);
    proof_assert!(old_inv.invariant(^*old_token_inner_g)); // Manually force we uphold the invariant
    (token, data, *next)
}

#[requires(curr != Ptr::null_logic())]
#[requires((**token).inv().curr == curr)]
#[ensures(Seq::singleton(*result.0).concat(inv_token_seq(*^token)).ext_eq(inv_token_seq(**token)))]
#[ensures(Seq::singleton(^result.0).concat(inv_token_seq(^^token)).ext_eq(inv_token_seq(^*token)))]
#[ensures(result.1 == (*^token).inv().curr)]
fn step_token_inplace<'o, 'i, T>(token: &'o mut &'i mut InvToken<T>, curr: Ptr<T>) -> (&'i mut T, Ptr<T>) {
    use crate::mem::uninit::*;
    let g = transmute_to_guard(MaybeUninitTFn, AssumeInitTFn, token);
    let old_inv = ghost!(g.inv());
    let m = &mut g.data;
    let old_token = m.take();
    let old_token_g = ghost!(old_token);
    let (new_token, data, ptr) = step_token(old_token, curr);
    proof_assert!(Seq::singleton(*data).concat(inv_token_seq(*new_token)).ext_eq(inv_token_seq(**old_token_g)));
    m.write(new_token);
    proof_assert!(old_inv.invariant(^m)); // Manually force we uphold the invariant
    (data, ptr)
}

impl<'a, T> IterMut<'a, T> {

    #[predicate]
    pub fn invariant(self) -> bool {
        self.curr == self.token.inv().curr
    }

    #[logic]
    #[requires(self.invariant())]
    //#[ensures(result.len() == self.token.data.model().len())]
    pub fn curr_seq(self) -> Seq<T> {
        inv_token_seq(*self.token)
    }

    #[logic]
    #[requires(self.invariant())]
    pub fn fut_seq(self) -> Seq<T> {
        pearlite!{inv_token_seq(^self.token)}
    }

    #[requires((*self).invariant())]
    #[ensures((*self).curr_seq().len() == 0 ==> result == None && *self == ^self)]
    #[ensures((*self).curr_seq().len() != 0 ==> match result {
        None => false,
        Some(elt) => Seq::singleton(*elt).concat((^self).curr_seq()).ext_eq((*self).curr_seq()) &&
            Seq::singleton(^elt).concat((^self).fut_seq()).ext_eq((*self).fut_seq())
    })]
    #[ensures((^self).invariant())]
    pub fn next(&mut self) -> Option<&'a mut T> {
        let old_self = ghost!(self);
        let IterMut { curr, token, ..} = self;
        if curr.is_null() {
            None
        } else {
            let (data, next) = step_token_inplace(token, *curr);
            *curr = next;
            Some(data)
        }
    }

    #[requires(self.invariant())]
    #[ensures(self.curr_seq() == self.fut_seq())]
    pub fn drop(self) {
        let IterMut { curr, token, ..} = self;
    }
}
