use creusot_contracts::*;
use crate::helpers::unwrap;
use crate::p_map::PMap;

struct UnionFind(Vec<isize>);
type FSet<T> = PMap<T, ()>;

// #[logic]
// #[variant(elems.len())]
// fn size_sum(elems: Seq<isize>) -> Int {
//     if elems.len() == 0 {
//         0
//     } else {
//         let head = elems.last().model();
//         size_sum(elems.upto_last()) + head.min(0)
//     }
// }

#[logic]
#[requires(n >= 0)]
#[variant(n)]
#[ensures(forall <i: Int> (0 <= i && i < n) == result.contains(i))]
fn set_upto(n: Int) -> FSet<Int> {
    if n == 0 {
        FSet::empty()
    } else {
        set_upto(n-1).insert(n-1, ())
    }
}

#[logic]
#[ensures(available.contains(elt) && @seq[elt] < 0 ==> result == Some(elt))]
#[ensures(match result {Some(r) => available.contains(r) && @seq[r] < 0, None => true})]
#[ensures(result != None ==> available.contains(elt))]
#[variant(available.len())]
fn raw_find(seq: Seq<isize>, elt: Int, available: FSet<Int>) -> Option<Int> {
    let next = seq[elt].model();
    if !available.contains(elt) {
        None
    } else if next < 0 {
        Some(elt)
    } else {
        raw_find(seq, next, available.remove(elt))
    }
}

#[law]
#[variant(av1.len())]
#[requires(forall<i: Int> av1.contains(i) ==> av2.contains(i))]
#[requires(raw_find(seq, elt, av1) != None)]
#[ensures(raw_find(seq, elt, av1) == raw_find(seq, elt, av2))]
fn raw_find_lemma(seq: Seq<isize>, elt: Int, av1: FSet<Int>, av2: FSet<Int>) {
    let next = seq[elt].model();
    if next >= 0 && av1.contains(elt) {
        raw_find_lemma( seq, next, av1.remove(elt), av2.remove(elt))
    }
}

#[predicate]
fn invariant_at(seq: Seq<isize>, i: Int) -> bool {
    seq[i].model() < seq.len() && raw_find(seq, i, set_upto(seq.len())) != None
}

#[predicate]
pub fn invariant(seq: Seq<isize>) -> bool {
    seq.len() <= isize::MAX.model() &&
        pearlite!{forall<i: Int> 0 <= i && i < seq.len() ==> invariant_at(seq, i)}
}

#[logic]
#[requires(invariant(seq))]
#[requires(0 <= elt && elt < seq.len())]
#[ensures(0 <= result && result < seq.len())]
#[ensures(@seq[elt] < 0 ==> result == elt)]
#[ensures(@seq[elt] >= 0 ==> result == unwrap(raw_find(seq, @seq[elt], set_upto(seq.len()).remove(elt))))]
#[ensures(@seq[elt] >= 0 ==> result == unwrap(raw_find(seq, @seq[elt], set_upto(seq.len()))))]
pub fn find_logic(seq: Seq<isize>, elt: Int) -> Int {
    raw_find_lemma;
    unwrap(raw_find(seq, elt, set_upto(seq.len())))
}

#[law]
#[requires(invariant(seq))]
#[requires(available.subset(set_upto(seq.len())))]
#[requires(@seq[dst] < 0 && @seq[@new_val] < 0)]
#[requires(0 <= dst && dst < seq.len())]
#[requires(raw_find(seq, elt, available) != None)]
#[requires(available.contains(@new_val))]
//#[requires(dst != @new_val)] // (for some reason this makes every take way longer so we use it as an implication instead)
#[variant(available.len())]
#[ensures(result)]
#[ensures(dst != @new_val && dst == find_logic(seq, elt) ==> raw_find(seq.set(dst, new_val), elt, available) == Some(@new_val))]
#[ensures(dst != find_logic(seq, elt) ==> raw_find(seq.set(dst, new_val), elt, available) == raw_find(seq, elt, available))]
#[ensures(invariant_at(seq, elt))]
pub fn find_set_lemma(seq: Seq<isize>, available: FSet<Int>, elt: Int, dst: Int, new_val: isize) -> bool{
    raw_find_lemma;
    let next = seq[elt].model();
    if next >= 0 {
        find_logic(seq, next); // important for triggering
        find_set_lemma(seq, available.remove(elt), next, dst, new_val)
    } else if elt == dst && dst != new_val.model() {
        raw_find(seq.set(dst, new_val), elt, available) ==
            raw_find(seq.set(dst, new_val),new_val.model(), available.remove(elt))
    } else {
        true
    }
}

impl UnionFind {
    #[predicate]
    pub fn invariant(self) -> bool {
        invariant(self.0.model())
    }

    #[logic]
    pub fn len(self) -> Int {
        self.0.model().len()
    }

    #[logic]
    #[requires(self.invariant())]
    pub fn find_logic(self, elt: Int) -> Int {
        find_logic(self.0.model(), elt)
    }

    #[logic]
    #[requires(self.invariant())]
    pub fn same_set(self, elt1: Int, elt2: Int) -> bool {
        self.find_logic(elt1) == self.find_logic(elt2)
    }

    #[requires(@len <= @isize::MAX)]
    #[ensures(result.invariant())]
    #[ensures(result.len() == @len)]
    #[ensures(forall<i: Int> 0 <= i && i < result.len() ==> result.find_logic(i) == i)]
    pub fn new(len: usize) -> Self {
        let mut v: Vec<isize> = Vec::with_capacity(len);
        #[invariant(val, forall<i: Int> 0 <= i && i < (@v).len() ==> @(@v)[i] == -1)]
        #[invariant(step, (@v).len() <= @len)]
        while v.len() < len {
            v.push(0-1)
        }
        UnionFind(v)
    }


    #[requires(self.invariant())]
    #[requires(@elt < self.len())]
    #[ensures(@result == self.find_logic(@elt))]
    pub fn find(&self, elt: usize) -> usize {
        let next = self.0[elt];
        if next < 0 {
            proof_assert!(@elt == self.find_logic(@elt));
            elt
        } else {
            self.find(next as usize)
        }
    }

    #[requires((*self).invariant())]
    #[requires(@elt1 < self.len() && @elt2 < self.len())]
    #[ensures((^self).invariant())]
    #[ensures(forall<i: Int> 0 <= i && i < self.len() ==>
        if (*self).same_set(i, @elt1) || (*self).same_set(i, @elt2) {
            (^self).find_logic(i) == @result.0
        } else {
            (^self).find_logic(i) == (*self).find_logic(i)
        })]
    #[ensures(result.1 == !(*self).same_set(@elt2, @elt1))]
    #[ensures((^self).len() == (*self).len())]
    #[ensures(@result.0 == (*self).find_logic(@elt1) || @result.0 == (*self).find_logic(@elt2))]
    pub fn union(&mut self, elt1: usize, elt2: usize) -> (usize, bool) {
        find_set_lemma;
        raw_find_lemma;
        let rep1 = self.find(elt1);
        proof_assert!(@(@self.0)[@rep1] < 0);
        let rep2 = self.find(elt2);
        proof_assert!(@(@self.0)[@rep2] < 0);
        if rep1 != rep2 {
            let rep1i = rep1 as isize;
            proof_assert!(forall<i: Int> 0 <= i && i < self.len() ==> find_set_lemma(@self.0, set_upto(self.len()), i, @rep2, rep1i));
            let old_self = ghost!(self);
            proof_assert!(invariant((@old_self.0).set(@rep2, rep1i)));
            self.0[rep2] = rep1i;
            proof_assert!((@old_self.0).set(@rep2, rep1i).ext_eq(@self.0)); //Sadly index mut spec doesn't make the guarantee
            (rep1, true)
        } else {
            (rep1, false)
        }
    }
}

fn test() {
    let mut uf = UnionFind::new(5);
    assert!(uf.union(0, 1).1);
    assert!(uf.union(2, 3).1);
    proof_assert!(uf.find_logic(4) == 4);
    let (elt, b) = uf.union(0, 3);
    proof_assert!(uf.find_logic(4) == 4);
    assert!(b);
    assert!(uf.find(1) == elt);
    assert!(uf.find(2) == elt);
    proof_assert!(@elt != 4);
    assert!(uf.find(4) != elt);
    assert!(!uf.union(1, 3).1)
}