use creusot_contracts::{*, logic::*};
use ::std::collections::btree_set::BTreeSet;
use creusot_contracts::std::iter::Iterator;
use crate::ghost_ptr::*;
use crate::p_map::PMap;

struct Node<T>{data: T, neighbours: Vec<NodePtr<T>>}
type NodePtr<T> = GhostPtr<Node<T>>;
type Token<T> = GhostToken<Node<T>>;
type TokenM<T> = PMap<NodePtr<T>, Node<T>>;
type SetM = <HashSetUsize as ShallowModel>::ShallowModelTy;
struct Graph<T>{token: Token<T>, start: NodePtr<T>}

#[predicate]
fn neighbours_invariant<T>(neighbours: Seq<NodePtr<T>>, token: TokenM<T>) -> bool {
    pearlite!{forall<i: Int> 0 <= i && i < neighbours.len() ==> token.contains(neighbours[i])}
}

impl<T> Graph<T> {
    #[predicate]
    pub fn invariant(self) -> bool {
        let token = self.token.shallow_model();
        pearlite!{token.contains(self.start) &&
            forall<ptr: NodePtr<T>> token.contains(ptr) ==>
                neighbours_invariant(@token.lookup(ptr).neighbours, token)}
    }
}

struct DFSMut<'a, T> {
    todo: Vec<NodePtr<T>>,
    seen: HashSetUsize,
    token: &'a mut Token<T>
}

#[predicate]
fn weak_neighbours_invariant<T>(neighbours: Seq<NodePtr<T>>, token: TokenM<T>, seen: SetM) -> bool {
    pearlite!{forall<i: Int> 0 <= i && i < neighbours.len() && !seen.contains(neighbours[i].addr_logic())
        ==> token.contains(neighbours[i])}
}

#[logic]
#[requires(weak_neighbours_invariant(neighbours, token, seen))]
#[requires(seen.contains(remove.addr_logic()))]
#[ensures(weak_neighbours_invariant(neighbours, token.remove(remove), seen) ==> result)]
#[ensures(result ==> weak_neighbours_invariant(neighbours, token.remove(remove), seen))]
fn weak_neighbours_lemma<T>(neighbours: Seq<NodePtr<T>>, token: TokenM<T>, seen: SetM, remove: NodePtr<T>) -> bool {
    true
}

#[predicate]
#[variant(todo.len())]
fn todo_invariant<T>(todo: Seq<NodePtr<T>>, seen: SetM, token: TokenM<T>) -> bool {
    if todo.len() == 0 {
        true
    } else {
        let last = todo.last();
        token.contains(last) && seen.contains(last.addr_logic()) &&
            todo_invariant(todo.upto_last(), seen, token.remove(last))
    }
}

#[predicate]
#[variant(todo.len())]
#[requires(todo_invariant(todo, seen, token))]
#[requires(!seen.contains(ptr.addr_logic()))]
#[ensures(result)]
#[ensures(result ==> todo_invariant(todo, seen.insert(ptr.addr_logic()), token.remove(ptr)))]
fn todo_lemma<T>(todo: Seq<NodePtr<T>>, seen: SetM, token: TokenM<T>, ptr: NodePtr<T>) -> bool {
    if todo.len() == 0 {
        true
    } else {
        todo_lemma(todo.upto_last(), seen, token.remove(todo.last()), ptr) &&
            token.remove(todo.last()).remove(ptr).ext_eq(token.remove(ptr).remove(todo.last()))
    }
}

#[law]
#[ensures(s.push(t).upto_last().ext_eq(s))]
fn dummy_lemma<T>(s: Seq<T>, t: T) {}

impl<'a, T> DFSMut<'a, T> {
    #[predicate]
    pub fn invariant(self) -> bool {
        let DFSMut{todo, seen, token} = self;
        pearlite!{todo_invariant(@todo, @seen, @token) &&
            forall<ptr: NodePtr<T>> (@token).contains(ptr) ==>
                weak_neighbours_invariant(@(@token).lookup(ptr).neighbours, @token, @seen)}
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    pub fn next(&mut self) -> Option<&mut T> {
        let DFSMut{todo, seen, token} = self;
        match todo.pop() {
            Some(ptr) => {
                proof_assert!(forall<neighbours: Seq<NodePtr<T>>> weak_neighbours_lemma(neighbours, @token, @seen, ptr));
                let old_token = ghost!(token.shallow_model());
                let Node{data, ref neighbours} = ptr.reborrow(token);
                proof_assert!(todo_invariant(@todo, @seen, @token));
                let mut i = 0;
                #[invariant(inv, DFSMut{todo: *todo, seen: *seen, token: *token}.invariant())]
                #[invariant(neighbours, weak_neighbours_invariant(@neighbours, @token, @seen))]
                #[invariant(future, ^self == DFSMut{todo: ^todo, seen: ^seen, token: ^token})]
                while i < neighbours.len() {
                    let neighbour = neighbours[i];
                    proof_assert!(!(@seen).contains(neighbour.addr_logic()) ==> (@token).contains(neighbour));
                    let old_seen = ghost!(seen.shallow_model());
                    if seen.insert(neighbour.addr()) {
                        proof_assert!(todo_lemma(@todo, *old_seen, @token, neighbour));
                        ghost!(dummy_lemma(todo.shallow_model(), neighbour));
                        todo.push(neighbour);
                        proof_assert!(todo_invariant(@todo, @seen, @token));
                    } else {
                        proof_assert!(*old_seen == @seen);
                    }
                    i+=1;
                }
                Some(data)
            }
            None => None
        }
    }
}



use ::std::collections::HashSet;

#[trusted]
struct HashSetUsize(HashSet<usize>);

impl ShallowModel for HashSetUsize {
    type ShallowModelTy = FSet<Int>;

    #[trusted]
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        absurd
    }
}

impl HashSetUsize {
    #[trusted]
    #[ensures(@result == FSet::EMPTY)]
    fn new() -> Self {
        HashSetUsize(HashSet::new())
    }

    #[trusted]
    #[ensures(result == (@self).contains(@val))]
    fn contains(&self, val: usize) -> bool {
        self.0.contains(&val)
    }

    #[trusted]
    #[ensures(result == !(@*self).contains(@val))]
    #[ensures(@^self == (@*self).insert(@val))]
    fn insert(&mut self, val: usize) -> bool {
        self.0.insert(val)
    }

    #[trusted]
    #[ensures(result == (@*self).contains(@val))]
    #[ensures(@^self == (@*self).remove(@val))]
    fn remove(&mut self, val: usize) -> bool {
        self.0.remove(&val)
    }
}