use crate::ghost_ptr::*;
use crate::helpers::{assert, unwrap};
use crate::p_map::PMap;
use creusot_contracts::{logic as base_logic, prusti_prelude::*};

struct Node<K> {
    key: K,
    nexts: Vec<Ptr<K>>,
}

type Ptr<K> = GhostPtr<Node<K>>;
type Token<K> = GhostToken<Node<K>>;
type TokenM<K> = PMap<Ptr<K>, Node<K>>;

/// If there is a skip-list segmented at `level` from `ptr` to `end` in `token` returns the subset of `token` that wasn't needed
/// Otherwise returns None
#[base_logic]
#[requires(level >= -1)]
#[variant(level + token.len())]
#[ensures(ptr == end ==> result == Some(token))]
#[ensures(level == -1 && ptr != end && token.contains(ptr) ==> result == Some(token.remove(ptr)))]
#[ensures(ptr != end && result != None ==> token.contains(ptr) && !unwrap(result).contains(ptr) && unwrap(result).len() < token.len())]
#[ensures(result != None ==> unwrap(result).subset(token))]
fn lseg<K>(ptr: Ptr<K>, end: Ptr<K>, token: TokenM<K>, level: Int) -> Option<TokenM<K>> {
    if ptr == end {
        Some(token)
    } else if level == -1 {
        if token.contains(ptr) {
            Some(token.remove(ptr))
        } else {
            None
        }
    } else {
        match token.get(ptr) {
            None => None,
            Some(node) => {
                let nexts = node.nexts.shallow_model();
                match (
                    nexts.len() > level && nexts[level] != ptr,
                    lseg(ptr, nexts[level], token, level - 1),
                ) {
                    (true, Some(token)) => lseg(nexts[level], end, token, level),
                    _ => None,
                }
            }
        }
    }
}

#[base_logic]
#[requires(level >= -1)]
#[requires(lseg(ptr, end, token, level) != None)]
fn lseg_basis<K>(ptr: Ptr<K>, end: Ptr<K>, token: TokenM<K>, level: Int) -> TokenM<K> {
    token.subtract(unwrap(lseg(ptr, end, token, level)))
}

/// Lemma for framing `lseg` when using a different `token`
#[logic(('_, '_, '_, '_, '_) -> '_)]
#[variant(token1.len() + level + 1)]
#[requires(level >= -1)]
#[requires(lseg(ptr, other, token1, level) != None)]
#[requires(lseg_basis(ptr, other, token1, level).disjoint(token2))]
#[ensures(result)]
#[ensures(lseg(ptr, other, lseg_basis(ptr, other, token1, level).union(token2), level) != None)]
#[ensures(result ==> unwrap(lseg(ptr, other, lseg_basis(ptr, other, token1, level).union(token2), level))
            .ext_eq(token2))]
fn lseg_super<K>(
    ptr: Ptr<K>,
    other: Ptr<K>,
    token1: TokenM<K>,
    token2: TokenM<K>,
    level: Int,
) -> bool {
    if ptr == other {
        true
    } else if level == -1 {
        token1
            .subtract(token1.remove(ptr))
            .union(token2)
            .remove(ptr)
            .ext_eq(token2)
    } else {
        let next = token1.lookup(ptr).nexts.shallow_model()[level];
        let rest = unwrap(lseg(ptr, next, token1, level - 1));
        let basis_diff = lseg_basis(next, other, rest, level).union(token2);
        lseg_basis(ptr, next, token1, level - 1)
            .union(basis_diff)
            .ext_eq(lseg_basis(ptr, other, token1, level).union(token2))
        && lseg_super(ptr, next, token1, basis_diff, level - 1)
        && lseg_super(next, other, rest, token2, level)
    }
}

/// Lemma for modifying the first element of the segment at a high enough level and framing `lseg`
#[logic(('_, '_, '_, '_, '_) -> '_)]
#[variant(level + 1)]
#[requires(level >= -1)]
#[requires(lseg(ptr, end, token1, level) != None)]
#[requires(token2.remove(ptr).ext_eq(token1.remove(ptr)))]
#[requires(token2.contains(ptr) && (@token2.lookup(ptr).nexts).len() > level)]
#[requires(forall<i: Int> 0 <= i && i <= level ==> (@token2.lookup(ptr).nexts)[i] == (@token1.lookup(ptr).nexts)[i])]
#[requires(ptr != end)]
#[ensures(result)]
#[ensures(lseg(ptr, end, token2, level) == lseg(ptr, end, token1, level))]
fn lseg_swap_first<K>(
    ptr: Ptr<K>,
    end: Ptr<K>,
    token1: TokenM<K>,
    token2: TokenM<K>,
    level: Int,
) -> bool {
    if level == -1 {
        true
    } else {
        let next = token1.lookup(ptr).nexts.shallow_model()[level];
        lseg_swap_first(ptr, next, token1, token2, level - 1)
    }
}

/// Lemma for concatenating skip lists
#[logic(('_, '_, '_, '_, '_) -> '_)]
#[variant(token.len())]
#[requires(level >= 0)]
#[requires(lseg(ptr1, ptr2, token, level) != None)]
#[requires(lseg(ptr2, ptr3, unwrap(lseg(ptr1, ptr2, token, level)), level) != None)]
#[requires(!token.contains(ptr3))]
#[ensures(result)]
#[ensures(!token.contains(ptr3) ==> lseg(ptr1, ptr3, token, level) == lseg(ptr2, ptr3, unwrap(lseg(ptr1, ptr2, token, level)), level))]
#[ensures(ptr1 != ptr2 ==> lseg(ptr1, ptr3, token, level) == lseg(ptr2, ptr3, unwrap(lseg(ptr1, ptr2, token, level)), level))]
#[ensures(lseg(ptr1, ptr3, token, level) == lseg(ptr2, ptr3, unwrap(lseg(ptr1, ptr2, token, level)), level))]
fn lseg_trans<K>(ptr1: Ptr<K>, ptr2: Ptr<K>, ptr3: Ptr<K>, token: TokenM<K>, level: Int) -> bool {
    TokenM::<K>::union_remove;
    if ptr1 != ptr2 {
        let Node { key: data, nexts } = token.lookup(ptr1);
        let next = nexts.shallow_model()[level];
        let token_rest = unwrap(lseg(ptr1, next, token, level - 1));
        lseg_trans(next, ptr2, ptr3, token_rest, level)
    } else {
        true
    }
}

/// Lemma for lowering the level used in `lseg`
#[logic(('_, '_, '_, '_) -> '_)]
#[variant(token.len() + level)]
#[requires(lseg(ptr1, ptr2, token, level) != None)]
#[requires(level >= 0)]
#[requires(!token.contains(ptr2))]
#[ensures(result)]
#[ensures(result && level > 0 ==> lseg(ptr1, ptr2, token, level) == lseg(ptr1, ptr2, token, level - 1))]
#[ensures(result ==> lseg(ptr1, ptr2, token, level) == lseg(ptr1, ptr2, token, 0))]
fn lseg_layered<K>(ptr1: Ptr<K>, ptr2: Ptr<K>, token: TokenM<K>, level: Int) -> bool {
    if ptr1 != ptr2 && level > 0 {
        let next = token.lookup(ptr1).nexts.shallow_model()[level];
        let token_rest = unwrap(lseg(ptr1, next, token, level - 1));
        lseg_layered(next, ptr2, token_rest, level)
            && lseg_trans(ptr1, next, ptr2, token, level - 1)
            && lseg_layered(ptr1, ptr2, token, level - 1)
    } else {
        true
    }
}

/// Recursive helper
/// Inserts key between `start` and `end` at `level` giving it height `new_level`
#[requires(lseg(start, end, @token, @level) != None)]
#[requires(start != end)]
#[requires(end == Ptr::null_logic() || unwrap(lseg(start, end, @token, @level)).contains(end))]
#[requires(new_level < usize::MAX)]
#[ensures(result.0 && new_level > level ==> lseg(start, result.1, @*token, @level) != None)]
#[ensures(result.0 && new_level > level ==> lseg(result.1, end, unwrap(lseg(start, result.1, @*token, @level)), @level) == old(lseg(start, end, @token, @level)))]
#[ensures(result.0 ==> !old(@token).contains(result.1) && (@*token).contains(result.1) && (@(@*token).lookup(result.1).nexts).len() == @new_level + 1)]
#[ensures((@(@*token).lookup(start).nexts).len() == old((@(@token).lookup(start).nexts).len()))]
#[ensures(!result.0 ==> *token == old(*token))]
#[ensures(lseg(start, end, @*token, @level) == old(lseg(start, end, @token, @level)))]
#[ensures(forall<i: Int> i > @new_level ==> (@(@*token).lookup(start).nexts).get(i) == (@old(@token).lookup(start).nexts).get(i))]
fn insert_between<K: Ord>(
    start: Ptr<K>,
    end: Ptr<K>,
    token: &mut Token<K>,
    level: usize,
    key: K,
    new_level: usize,
) -> (bool, Ptr<K>)
where
    K: DeepModel,
    K::DeepModelTy: OrdLogic,
{
    let old_token = ghost!(token.shallow_model());
    let next: Ptr<K> = start.borrow(token).nexts[level];
    if token.are_eq(next, end) || key < next.borrow(token).key {
        if level <= new_level {
            let (is_new, found) = if level == 0 {
                let new = Ptr::from_box_in(
                    Box::new(Node {
                        key,
                        nexts: vec![(Ptr::null()); new_level + 1],
                    }),
                    token,
                );
                proof_assert!(unwrap(lseg(new, next, unwrap(lseg(start, new, @token, @level - 1)), @level - 1)).ext_eq(unwrap(lseg(start, next, *old_token, @level - 1))));
                (true, new)
            } else {
                insert_between(start, next, token, level - 1, key, new_level)
            };
            if is_new {
                proof_assert!(start != found);
                proof_assert!(lseg(start, found, @token, @level - 1) != None);
                proof_assert!(lseg(found, next, unwrap(lseg(start, found, @token, @level - 1)), @level - 1) == lseg(start, next, *old_token, @level - 1));
                let t1 = ghost!(token.shallow_model());
                start.borrow_mut(token).nexts[level] = found;
                let t2 = ghost!(token.shallow_model());
                found.borrow_mut(token).nexts[level] = next;
                proof_assert!(lseg_swap_first(start, found, *t1, *t2, @level - 1));
                proof_assert!(lseg(start, found, *t1, @level - 1) == lseg(start, found, *t2, @level - 1));
                proof_assert!(lseg_super(start, found, *t2, (@token).subtract(lseg_basis(start, found, *t2, @level - 1)), @level - 1));
                proof_assert!(lseg(start, found, @token, @level - 1) != None);
                proof_assert!(lseg_swap_first(found, next, unwrap(lseg(start, found, *t1, @level - 1)), unwrap(lseg(start, found, @token, @level - 1)), @level - 1));
                proof_assert!(lseg(found, next, unwrap(lseg(start, found, @token, @level - 1)), @level - 1) == lseg(start, next, *old_token, @level - 1));
                proof_assert!(lseg(start, found, @token, @level) == lseg(start, found, @token, @level - 1));
                proof_assert!(lseg(found, next, unwrap(lseg(start, found, @token, @level)), @level) == lseg(start, next, *old_token, @level - 1));
                proof_assert!(lseg(start, next, *old_token, @level) == lseg(start, next, *old_token, @level - 1));
                proof_assert!(lseg(found, end, unwrap(lseg(start, found, @token, @level)), @level) == lseg(start, end, *old_token, @level));
                proof_assert!(lseg(start, end, @token, @level) == lseg(start, end, *old_token, @level));
                proof_assert!(forall<i: Int> i > @new_level ==> (@(@*token).lookup(start).nexts).get(i) == (@old(@token).lookup(start).nexts).get(i));
            }
            proof_assert!(lseg(start, end, @token, @level) == lseg(start, end, *old_token, @level));
            (is_new, found)
        } else {
            let lvm1 = level - 1;
            proof_assert!(next == Ptr::null_logic() || unwrap(lseg(start, next, @token, @lvm1)).contains(next));
            proof_assert!(@token == *old_token);
            let res = insert_between(start, next, token, lvm1, key, new_level);
            //proof_assert!((@token).get(next) == old_token.get(next));
            proof_assert!((@(@token).lookup(start).nexts)[@level] != start);
            // proof_assert!(unwrap(lseg(start, end, @token, @level)).ext_eq(unwrap(lseg(next, end, unwrap(lseg(start, next, @token, @level - 1)), @level))));
            proof_assert!((@token).get(next) == old_token.get(next) ==> lseg(start, end, @token, @level) == lseg(next, end, unwrap(lseg(start, next, @token, @level - 1)), @level));
            proof_assert!(lseg(start, next, @token, @lvm1) == lseg(start, next, *old_token, @lvm1));
            proof_assert!(@lvm1 == @level - 1);
            proof_assert!(lseg(start, next, @token, @level - 1) == lseg(start, next, *old_token, @level - 1));
            proof_assert!(lseg(start, end, @token, @level) == lseg(start, end, *old_token, @level));
            res
        }
    } else if key == next.borrow(token).key {
        (false, next)
    } else {
        let rest = ghost!(unwrap(lseg(start, next, *old_token, level.shallow_model() - 1.shallow_model())));
        let token_s = token.shrink(&rest);
        let (is_new, found) = insert_between(next, end, token_s, level, key, new_level);
        proof_assert!(lseg_super(start, next, *old_token, @token_s, @level - 1));
        proof_assert!(!is_new ==> old_token.ext_eq(@token));
        (is_new, found)
    }
}
