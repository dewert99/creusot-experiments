use creusot_contracts::{logic::*, prusti_prelude::*, logic as base_logic};
use super::helpers::*;

pub struct PMap<K, V: ?Sized>(pub Mapping<K, Option<SizedW<V>>>);


#[trusted]
#[logic(('_) -> '_)]
#[requires(forall<k: K> m.0.get(k) == None)]
#[ensures(result)]
#[ensures(result ==> m.len() == 0)]
fn len_def0<K, V: ?Sized>(m: PMap<K, V>) -> bool {true}

#[trusted]
#[logic(('_, '_) -> '_)]
#[requires(m.0.get(k) != None)]
#[ensures(result)]
#[ensures(result ==> m.len() == PMap(m.0.set(k, None)).len() + 1)]
fn len_def1<K, V: ?Sized>(m: PMap<K, V>, k: K) -> bool {true}




impl<K, V: ?Sized> PMap<K, V> {
    #[trusted]
    #[logic(('_) -> '_)]
    #[ensures(result >= 0)]
    pub fn len(self) -> Int {
        absurd
    }


    #[base_logic]
    #[creusot::prusti::home_sig="('x, '_, 'x) -> 'x"] // Hack while we don't support constructors
    #[ensures(self.contains(k) ==> result.len() == self.len())]
    #[ensures(!self.contains(k) ==> result.len() == self.len() + 1)]
    pub fn insert(self, k: K, v: V) -> Self {
        PMap(self.0.set(k, Some(v.make_sized()))).remove(k).ext_eq(self.remove(k));
        PMap(self.0.set(k, Some(v.make_sized())))
    }

    #[base_logic]
    #[creusot::prusti::home_sig="('x, '_) -> 'x"] // Hack while we don't support constructors
    #[ensures(result.len() == if self.contains(k) {self.len() - 1} else {self.len()})]
    pub fn remove(self, k: K) -> Self {
        len_def1(self, k);
        PMap(self.0.set(k, None))
    }

    #[logic(('x, '_) -> 'x)]
    #[why3::attr = "inline:trivial"]
    pub fn get(self, k: K) -> Option<SizedW<V>>{
        self.0.get(k)
    }

    #[logic(('x, '_) -> 'x)]
    pub fn lookup_unsized(self, k: K) -> SizedW<V> {
        unwrap(self.0.get(k))
    }

    #[logic(('x, '_) -> 'x)]
    pub fn lookup(self, k: K) -> V
        where V: Sized{
        *unwrap(self.0.get(k))
    }

    #[logic(('_, '_) -> '_)]
    pub fn contains(self, k: K) -> bool {
        self.0.get(k) != None
    }

    #[base_logic]
    #[creusot::prusti::home_sig="() -> '_"] // Hack while we don't support constructors
    //#[ensures(len_def0(result))]
    #[ensures(result.len() == 0)]
    pub fn empty() -> Self {
        PMap(Mapping::cst(None))
    }


    #[logic(('_) -> '_)]
    pub fn is_empty(self) -> bool {
        self.ext_eq(PMap::empty())
    }

    #[logic(('_, '_) -> '_)]
    pub fn disjoint(self, other: Self) -> bool {
        pearlite!{forall<k: K> !self.contains(k) || !other.contains(k)}
    }

    #[logic(('_, '_) -> '_)]
    pub fn subset(self, other: Self) -> bool {
        pearlite!{forall<k: K> self.contains(k) ==> other.get(k) == self.get(k)}
    }


    #[trusted]
    #[logic(('x, 'x) -> 'x)]
    #[requires(self.disjoint(other))]
    #[ensures(forall<k: K> result.get(k) == if self.contains(k) {
        self.get(k)
    } else if other.contains(k) {
        other.get(k)
    } else {
        None
    })]
    #[ensures(result.len() == self.len() + other.len())]
    pub fn union(self, other: Self) -> Self {
        absurd
    }

    #[logic(('_, '_, '_) -> '_)]
    #[requires(self.contains(k))]
    #[requires(self.disjoint(other))]
    #[ensures(result ==> self.remove(k).union(other) == self.union(other).remove(k))]
    #[ensures(result)]
    pub fn union_remove(self, other: Self, k: K) -> bool {
        self.remove(k).union(other).ext_eq(self.union(other).remove(k))
    }

    #[logic(('_, '_) -> '_)]
    #[ensures(result ==> self == other)]
    #[ensures((forall<k: K> self.0.get(k) == other.0.get(k)) ==> result)]
    pub fn ext_eq(self, other: Self) -> bool {
        self.0 == other.0
    }
}