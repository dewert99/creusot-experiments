use ::std::ops::Deref;
use creusot_contracts::*;
use crate::ghost_ptr::{GhostPtr, GhostToken};
use crate::p_map::PMap;

enum Node {
    Root{size: u64},
    Internal{parent: GhostPtr<Node>}
}

struct UnionFind(GhostToken<Node>);
type NodePtr = GhostPtr<Node>;
type TokenM = PMap<NodePtr, Node>;

#[predicate]
#[variant(union_find.len())]
fn owns(union_find: TokenM, ptr: NodePtr) -> bool {
    match union_find.get(ptr) {
        None => false,
        Some(node) => match node.deref() {
            Node::Root{..} => true,
            Node::Internal {parent} => owns(union_find.remove(ptr), *parent)
        }
    }
}

#[logic]
#[requires(owns(union_find, ptr))]
#[ensures(union_find.contains(result))]
#[ensures(match union_find.lookup(result) {Node::Root{..} => true, _ => false})]
#[variant(union_find.len())]
fn representative(union_find: TokenM, ptr: NodePtr) -> NodePtr {
    match union_find.lookup(ptr) {
        Node::Root{..} => ptr,
        Node::Internal {parent} => representative(union_find.remove(ptr), parent)
    }
}

#[law]
#[requires(owns(union_find, ptr))]
#[requires(union_find.subset(other))]
#[ensures(owns(other, ptr))]
#[ensures(representative(union_find, ptr) == representative(other, ptr))]
#[ensures(result)]
#[variant(union_find.len())]
fn owns_super(union_find: TokenM, other: TokenM, ptr: NodePtr) -> bool {
    match union_find.lookup(ptr) {
        Node::Root{..} => true,
        Node::Internal {parent} =>
            owns_super(union_find.remove(ptr), other.remove(ptr), parent)
    }
}

#[logic]
fn set_parent(union_find: TokenM, ptr1: NodePtr, ptr2: NodePtr) -> TokenM {
    union_find.insert(ptr1, Node::Internal {parent: ptr2})
}

#[law]
#[requires(owns(union_find, ptr3))]
#[requires(owns(union_find, ptr1) && representative(union_find, ptr1) == ptr1)]
#[requires(owns(union_find, ptr2) && representative(union_find, ptr2) == ptr2 && ptr2 != ptr1)]
#[ensures(result)]
#[ensures(owns(set_parent(union_find, ptr1, ptr2), ptr3))]
#[ensures(representative(union_find, ptr3) == ptr1
  ==> representative(set_parent(union_find, ptr1, ptr2), ptr3) == representative(union_find, ptr2))]
#[ensures(representative(union_find, ptr3) != ptr1
  ==> representative(set_parent(union_find, ptr1, ptr2), ptr3) == representative(union_find, ptr3))]
#[variant(union_find.len())]
fn owns_union(union_find: TokenM, ptr1: NodePtr, ptr2: NodePtr, ptr3: NodePtr) -> bool {
    owns_super;
    match union_find.lookup(ptr3) {
        Node::Root{..} => true,
        Node::Internal {parent} =>
            set_parent(union_find, ptr1, ptr2).remove(ptr3).ext_eq(set_parent(union_find.remove(ptr3), ptr1, ptr2)) &&
                owns_union(union_find.remove(ptr3), ptr1, ptr2, parent)
    }
}

#[logic]
fn compress(union_find: TokenM, ptr: NodePtr) -> TokenM {
    set_parent(union_find, ptr, representative(union_find, ptr))
}

#[law]
#[requires(owns(union_find, ptr1) && owns(sub_union_find, ptr2))]
#[requires(sub_union_find.subset(union_find))]
#[requires(match union_find.lookup(ptr1) {Node::Root{..} => false, _ => true})]
#[ensures(result)]
#[ensures(owns(set_parent(sub_union_find, ptr1, representative(union_find, ptr1)), ptr2))]
#[ensures(representative(set_parent(sub_union_find, ptr1, representative(union_find, ptr1)), ptr2) == representative(sub_union_find, ptr2))]
#[variant(sub_union_find.len())]
fn owns_compress(sub_union_find: TokenM, union_find: TokenM, ptr1: NodePtr, ptr2: NodePtr) -> bool {
    if ptr1 == ptr2 {
        owns_super(sub_union_find, union_find, ptr1)
    } else {
        match sub_union_find.lookup(ptr2) {
            Node::Root{..} => true,
            Node::Internal {parent} =>
                owns_compress(sub_union_find.remove(ptr2), union_find, ptr1, parent)
                    && set_parent(sub_union_find, ptr1, representative(union_find, ptr1)).remove(ptr2)
                    .ext_eq(set_parent(sub_union_find.remove(ptr2), ptr1, representative(union_find, ptr1)))
        }
    }
}

impl UnionFind {
    #[predicate]
    fn owns(self, ptr: NodePtr) -> bool {
        owns(self.0.model(), ptr)
    }

    #[logic]
    fn representative(self, ptr: NodePtr) -> NodePtr {
        representative(self.0.model(), ptr)
    }

    #[logic]
    fn same_set(self, ptr1: NodePtr, ptr2: NodePtr) -> bool {
        self.representative(ptr1) == self.representative(ptr2)
    }

    #[requires(self.owns(ptr))]
    #[ensures(forall<ptr3: NodePtr> (*self).owns(ptr3) ==>
        (^self).owns(ptr3) && (^self).representative(ptr3) == (*self).representative(ptr3))]
    #[ensures(result == self.representative(ptr))]
    fn find(&mut self, ptr: NodePtr) -> NodePtr {
        owns_compress;
        match ptr.borrow(&self.0) {
            Node::Root {..} => ptr,
            Node::Internal {parent} => {
                proof_assert!(owns_super(self.0.model().remove(ptr), self.0.model(), *parent));
                let rep = self.find(*parent);
                *ptr.borrow_mut(&mut self.0) = Node::Internal {parent: rep};
                rep
            }
        }
    }

    #[requires((*self).owns(ptr1) && (*self).owns(ptr2))]
    #[ensures(forall<ptr3: NodePtr> (*self).owns(ptr3) ==>
        (^self).owns(ptr3) &&
        if (*self).same_set(ptr3, ptr1) || (*self).same_set(ptr3, ptr2) {
            (^self).representative(ptr3) == result.0
        } else {
            (^self).representative(ptr3) == (*self).representative(ptr3)
        })]
    #[ensures(result.1 == !(*self).same_set(ptr1, ptr2))]
    #[ensures(result.0 == (*self).representative(ptr1) || result.0 == (*self).representative(ptr2))]
    fn union(&mut self, ptr1: NodePtr, ptr2: NodePtr) -> (NodePtr, bool) {
        owns_union;
        let rep1 = self.find(ptr1);
        let rep2 = self.find(ptr2);
        if rep1.addr() != rep2.addr() {
            *rep1.borrow_mut(&mut self.0) = Node::Internal {parent: rep2};
            (rep2, true)
        } else {
            proof_assert!(self.0.injective_lemma(rep1, rep2));
            (rep2, false)
        }
    }
}