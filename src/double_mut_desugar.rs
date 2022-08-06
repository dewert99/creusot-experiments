

use creusot_contracts::Int;
use creusot_contracts::*;
use creusot_contracts::stubs::*;
use crate::p_map::PMap;
use super::ghost_ptr::*;
fn make_mut<T>(curr: T, fin: T) -> &'static mut T {
    panic!()
}
fn fin<T>(m: &mut T) -> T {
    panic!() // forall X, Y. fin(make_mut(X, Y)) == Y
}
fn curr<T>(m: &mut T) -> T {
    panic!() // forall X, Y. curr(make_mut(X, Y)) == X
}
fn havoc<T>() -> T {
    panic!() // non deterministic arbitrary value
}
fn id<T>(r: &T) -> T {
    panic!() // forall X. id(X) == X
}
fn assume(a: bool){}
fn assume_eq<T>(a: T, b: T){}
macro_rules! assume {
    ($v1:expr ,= $v2:expr) => {assume_eq($v1, $v2)}; // `,=` is SMT equality
    ($cond:expr) => {assume($cond)};
}
macro_rules! assert {
    ($v1:expr ,= $v2:expr) => {assume_eq($v1, $v2)};
    ($cond:expr) => {assume($cond)};
}
fn test3() {
    let mut token = GhostToken::new();
    let ptr1 = GhostPtr::new_in(1, &mut token);
    let ptr2 = GhostPtr::new_in(2, &mut token);
    let ptr3 = GhostPtr::new_in(3, &mut token);
    let mut t = &mut token;
    let m1 = ptr1.reborrow(&mut t);
    let m2 = ptr2.reborrow(&mut t);
    let m3 = ptr3.reborrow(&mut t);
    *m2 *= 10;
    *m1 *= 10;
    *m3 *= 10;
    let r3 = ptr3.borrow(&token);
    let r2 = ptr2.borrow(&token);
    let r1 = ptr1.borrow(&token);
    proof_assert!(@r1 == 10);
    proof_assert!(@r2 == 20);
    proof_assert!(@r3 == 30);
    proof_assert!(false);
}
// Prophesy Encoding
fn test3a() {
    let mut token = GhostToken::new();
    let tmp = make_mut(token, havoc());
    token = fin(tmp);
    let ptr1 = GhostPtr::new_in(1, tmp);
    let tmp = make_mut(token, havoc());
    token = fin(tmp);
    let ptr2 = GhostPtr::new_in(2, tmp);
    let tmp = make_mut(token, havoc());
    token = fin(tmp);
    let ptr3 = GhostPtr::new_in(3, tmp);
    let tmp = make_mut(token, havoc());
    token = fin(tmp);
    let mut t = tmp;
    let tmp = make_mut(t, havoc());
    t = fin(tmp);
    let m1 = ptr1.reborrow(tmp);
    let tmp = make_mut(t, havoc());
    t = fin(tmp);
    let m2 = ptr2.reborrow(tmp);
    let tmp = make_mut(t, havoc());
    t = fin(tmp);
    let m3 = ptr3.reborrow(tmp);
    let m2 = make_mut(curr(m2) * 10, fin(m2));
    assume!(curr(m2) ,= fin(m2)); // drop m2
    let m1 = make_mut(curr(m1) * 10, fin(m1));
    assume!(curr(m1) ,= fin(m1)); // drop m1
    let m3 = make_mut(curr(m3) * 10, fin(m3));
    assume!(curr(m3) ,= fin(m3)); // drop m3
    assume!(curr(t) ,= fin(t)); // drop t
    let r3 = ptr3.borrow(&token);
    let r2 = ptr2.borrow(&token);
    let r1 = ptr1.borrow(&token);
    proof_assert!(@r1 == 10);
    proof_assert!(@r2 == 20);
    proof_assert!(@r3 == 30);
    proof_assert!(false);
}
// SSA
fn test3b() {
    let token_0 = GhostToken::new();
    let tmp_0 = make_mut(token_0, havoc());
    let token_1 = fin(tmp_0);
    let ptr1 = GhostPtr::new_in(1, tmp_0);
    let tmp_1 = make_mut(token_1, havoc());
    let token_2 = fin(tmp_1);
    let ptr2 = GhostPtr::new_in(2, tmp_1);
    let tmp_2 = make_mut(token_2, havoc());
    let token_3 = fin(tmp_2);
    let ptr3 = GhostPtr::new_in(3, tmp_2);
    let tmp_3 = make_mut(token_3, havoc());
    let token_4 = fin(tmp_3);
    let t_0 = tmp_3;
    let tmp_4 = make_mut(t_0, havoc());
    let t_1 = fin(tmp_4);
    let m1_0 = ptr1.reborrow(tmp_4);
    let tmp_5 = make_mut(t_1, havoc());
    let t_2 = fin(tmp_5);
    let m2_0 = ptr2.reborrow(tmp_5);
    let tmp_6 = make_mut(t_2, havoc());
    let t_3 = fin(tmp_6);
    let m3_0 = ptr3.reborrow(tmp_6);
    let m2_1 = make_mut(curr(m2_0) * 10, fin(m2_0));
    assume!(curr(m2_1) ,= fin(m2_1)); // drop m2
    let m1_1 = make_mut(curr(m1_0) * 10, fin(m1_0));
    assume!(curr(m1_1) ,= fin(m1_1)); // drop m1
    let m3_1 = make_mut(curr(m3_0) * 10, fin(m3_0));
    assume!(curr(m3_1) ,= fin(m3_1)); // drop m3
    assume!(curr(t_3) ,= fin(t_3)); // drop t
    let r3 = ptr3.borrow(&token_4);
    let r2 = ptr2.borrow(&token_4);
    let r1 = ptr1.borrow(&token_4);
    proof_assert!(@r1 == 10);
    proof_assert!(@r2 == 20);
    proof_assert!(@r3 == 30);
    proof_assert!(false);
}
// VC Generation
fn test3c() {
    let (token_0, token_1, token_2, token_3, token_4) = havoc();
    let (ptr1, ptr2, ptr3) = havoc();
    let (t_0, t_1, t_2, t_3) = havoc();
    let (tmp_0, tmp_1, tmp_2, tmp_3, tmp_4, tmp_5, tmp_6) = havoc();
    let (m1_0, m1_1, m2_0, m2_1, m3_0, m3_1, r1, r2, r3) = havoc();
    assume!(token_0.model() ,= PMap::empty());
    assume!(tmp_0 ,= make_mut(token_0, havoc()));
    assume!(token_1 ,= fin(tmp_0));
    assume!(!curr(tmp_0).model().contains(ptr1));
    assume!(fin(tmp_0).model() ,= curr(tmp_0).model().insert(ptr1, 1));
    assume!(tmp_1 ,= make_mut(token_1, havoc()));
    assume!(token_2 ,= fin(tmp_1));
    assume!(!curr(tmp_1).model().contains(ptr2));
    assume!(fin(tmp_1).model() ,= curr(tmp_1).model().insert(ptr2, 2));
    assume!(tmp_2 ,= make_mut(token_2, havoc()));
    assume!(token_3 ,= fin(tmp_2));
    assume!(!curr(tmp_2).model().contains(ptr3));
    assume!(fin(tmp_2).model() ,= curr(tmp_2).model().insert(ptr3, 1));
    assume!(tmp_3 ,= make_mut(token_3, havoc()));
    assume!(token_4 ,= fin(tmp_3));
    assume!(t_0 ,= tmp_3);
    assume!(tmp_4 ,= make_mut(t_0, havoc()));
    assume!(t_1 ,= fin(tmp_4));
    assert!(curr(curr(tmp_4)).model().contains(ptr1));
    assume!(curr(m1_0) ,= curr(curr(tmp_4)).model().lookup(ptr1));
    assume!(curr(fin(tmp_4)).model() ,= curr(curr(tmp_4)).model().remove(ptr1));
    assume!(fin(curr(tmp_4)).model() ,= fin(fin(tmp_4)).model().insert(ptr1, fin(m1_0)));
    assume!(tmp_5 ,= make_mut(t_1, havoc()));
    assume!(t_2 ,= fin(tmp_5));
    assert!(curr(curr(tmp_5)).model().contains(ptr2));
    assume!(curr(m2_0) ,= curr(curr(tmp_5)).model().lookup(ptr2));
    assume!(curr(fin(tmp_5)).model() ,= curr(curr(tmp_5)).model().remove(ptr2));
    assume!(fin(curr(tmp_5)).model() ,= fin(fin(tmp_5)).model().insert(ptr1, fin(m2_0)));
    assume!(tmp_6 ,= make_mut(t_2, havoc()));
    assume!(t_3 ,= fin(tmp_6));
    assert!(curr(curr(tmp_6)).model().contains(ptr3));
    assume!(curr(m3_0) ,= curr(curr(tmp_6)).model().lookup(ptr3));
    assume!(curr(fin(tmp_6)).model() ,= curr(curr(tmp_6)).model().remove(ptr3));
    assume!(fin(curr(tmp_6)).model() ,= fin(fin(tmp_6)).model().insert(ptr1, fin(m3_0)));
    assume!(m2_1 ,= make_mut(curr(m2_0) * 10, fin(m2_0)));
    assume!(curr(m2_1) ,= fin(m2_1)); // drop m2
    assume!(m1_1 ,= make_mut(curr(m1_0) * 10, fin(m1_0)));
    assume!(curr(m1_1) ,= fin(m1_1)); // drop m1
    assume!(m3_1 ,= make_mut(curr(m3_0) * 10, fin(m3_0)));
    assume!(curr(m3_1) ,= fin(m3_1)); // drop m3
    assume!(curr(t_3) ,= fin(t_3)); // drop t
    assert!(id(&token_4).model().contains(ptr3));
    assume!(id(r3) ,= id(&token_4).model().lookup(ptr3));
    assert!(id(&token_4).model().contains(ptr2));
    assume!(id(r2) ,= id(&token_4).model().lookup(ptr2));
    assert!(id(&token_4).model().contains(ptr1));
    assume!(id(r1) ,= id(&token_4).model().lookup(ptr1));
    assert!(id(r1).model() ,= 10.model());
    assert!(id(r2).model() ,= 20.model());
    assert!(id(r3).model() ,= 30.model());
    assert!(false);
}
// Simplification
fn test3d() {
    type GT = GhostToken<i32>;
    let (token_0, token_1, token_2, token_3, token_4): (GT, GT, GT, GT, GT) = havoc();
    let (ptr1, ptr2, ptr3) = havoc();
    let (t_0, t_1, t_2, t_3): (&mut GT, &mut GT, &mut GT, &mut GT) = havoc();
    let (tmp_3) = havoc();
    let (m1_0, m2_0, m3_0, r1, r2, r3) = havoc();
    assume!(token_0.model() ,= PMap::empty());
    assume!(!token_0.model().contains(ptr1));
    assume!(token_1.model() ,= token_0.model().insert(ptr1, 1));
    assume!(!token_1.model().contains(ptr2));
    assume!(token_2.model() ,= token_1.model().insert(ptr2, 2));
    assume!(!token_2.model().contains(ptr3));
    assume!(token_3.model() ,= token_2.model().insert(ptr3, 1));
    assume!(tmp_3 ,= make_mut(token_3, havoc()));
    assume!(token_4 ,= fin(tmp_3));
    assume!(t_0 ,= tmp_3);
    assert!(curr(t_0).model().contains(ptr1));
    assume!(curr(m1_0) ,= curr(t_0).model().lookup(ptr1));
    assume!(curr(t_1).model() ,= curr(t_0).model().remove(ptr1));
    assume!(fin(t_0).model() ,= fin(t_1).model().insert(ptr1, fin(m1_0)));
    assert!(curr(t_1).model().contains(ptr2));
    assume!(curr(m2_0) ,= curr(t_1).model().lookup(ptr2));
    assume!(curr(t_2).model() ,= curr(t_1).model().remove(ptr2));
    assume!(fin(t_1).model() ,= fin(t_2).model().insert(ptr1, fin(m2_0)));
    assert!(curr(t_2).model().contains(ptr3));
    assume!(curr(m3_0) ,= curr(t_2).model().lookup(ptr3));
    assume!(curr(t_3).model() ,= curr(t_2).model().remove(ptr3));
    assume!(fin(t_2).model() ,= fin(t_3).model().insert(ptr1, fin(m3_0)));
    assume!(curr(m2_0) * 10 ,= fin(m2_0));
    assume!(curr(m1_0) * 10 ,= fin(m1_0));
    assume!(curr(m3_0) * 10 ,= fin(m3_0));
    assume!(curr(t_3) ,= fin(t_3)); // drop t
    assert!(id(&token_4).model().contains(ptr3));
    assume!(id(r3) ,= id(&token_4).model().lookup(ptr3));
    assert!(id(&token_4).model().contains(ptr2));
    assume!(id(r2) ,= id(&token_4).model().lookup(ptr2));
    assert!(id(&token_4).model().contains(ptr1));
    assume!(id(r1) ,= id(&token_4).model().lookup(ptr1));
    assert!(id(r1).model() ,= 10.model());
    assert!(id(r2).model() ,= 20.model());
    assert!(id(r3).model() ,= 30.model());
    assert!(false);
}
// More Simplification
fn test3e() {
    type GT = GhostToken<i32>;
    let (token_0, token_1, token_2, token_3, token_4): (GT, GT, GT, GT, GT) = havoc();
    let (ptr1, ptr2, ptr3) = havoc();
    let (t_0, t_1, t_2, t_3): (&mut GT, &mut GT, &mut GT, &mut GT) = havoc();
    let (tmp_3) = havoc();
    let (m1_0, m2_0, m3_0, r1, r2, r3) = havoc();
    assume!(token_0.model() ,= PMap::empty());
    // token_0.model() = {}
    assume!(!token_0.model().contains(ptr1));
    assume!(token_1.model() ,= token_0.model().insert(ptr1, 1));
    // token_1.model() = {ptr1: 1}
    assume!(!token_1.model().contains(ptr2));
    assume!(token_2.model() ,= token_1.model().insert(ptr2, 2));
    // token_2.model() = {ptr1: 1, ptr2: 2}
    assume!(!token_2.model().contains(ptr3));
    assume!(token_3.model() ,= token_2.model().insert(ptr3, 1));
    // token_3.model() =  {ptr1: 1, ptr2: 2, ptr3: 3}
    assume!(tmp_3 ,= make_mut(token_3, havoc()));
    assume!(token_4 ,= fin(tmp_3));
    assume!(t_0 ,= tmp_3);
    // curr(t_0).model() = {ptr1: 1, ptr2: 2, ptr3: 3}
    assert!(curr(t_0).model().contains(ptr1));
    assume!(curr(m1_0) ,= curr(t_0).model().lookup(ptr1));
    // curr(m1_0) = 1
    assume!(curr(t_1).model() ,= curr(t_0).model().remove(ptr1));
    // curr(t_1).model() = {ptr2: 2, ptr3: 3}
    assume!(fin(t_0).model() ,= fin(t_1).model().insert(ptr1, fin(m1_0)));
    assert!(curr(t_1).model().contains(ptr2));
    assume!(curr(m2_0) ,= curr(t_1).model().lookup(ptr2));
    // curr(m2_0) = 2
    assume!(curr(t_2).model() ,= curr(t_1).model().remove(ptr2));
    // curr(t_2).model() = {ptr3: 3}
    assume!(fin(t_1).model() ,= fin(t_2).model().insert(ptr1, fin(m2_0)));
    assert!(curr(t_2).model().contains(ptr3));
    assume!(curr(m3_0) ,= curr(t_2).model().lookup(ptr3));
    // curr(m3_0)= 3
    assume!(curr(t_3).model() ,= curr(t_2).model().remove(ptr3));
    // curr(t_3).model() = {}
    assume!(fin(t_2).model() ,= fin(t_3).model().insert(ptr1, fin(m3_0)));
    assume!(curr(m2_0) * 10 ,= fin(m2_0));
    // fin(m2_0).model() = 20
    assume!(curr(m1_0) * 10 ,= fin(m1_0));
    // fin(m1_0).model() = 10
    assume!(curr(m3_0) * 10 ,= fin(m3_0));
    // fin(m3_0).model() = 30
    assume!(curr(t_3) ,= fin(t_3)); // drop t
    // fin(t_3).model() = {}
    // NOTE
    // token_4.model()
    // == fin(tmp_3).model() (321)
    // == fin(t_0).model() (322)
    // == fin(t_1).model().insert(ptr1, fin(m1_0)) (330)
    // == fin(t_1).model().insert(ptr1, 10) (351)
    // == fin(t_2).model().insert(ptr1, fin(m2_0)).insert(ptr1, 10) (337)
    // == fin(t_2).model().insert(ptr2, 20).insert(ptr1, 10) (349)
    // == fin(t_3).model().insert(ptr1, fin(m3_0)).insert(ptr2, 20).insert(ptr1, 10) (344)
    // == fin(t_3).model().insert(ptr1, 30).insert(ptr2, 20).insert(ptr1, 10) (346)
    // == {}.insert(ptr3, 30).insert(ptr2, 20).insert(ptr1, 10) (353)
    // == {ptr1: 10, ptr2: 20, ptr: 30}
    assert!(id(&token_4).model().contains(ptr3));
    assume!(id(r3) ,= id(&token_4).model().lookup(ptr3));
    assert!(id(&token_4).model().contains(ptr2));
    assume!(id(r2) ,= id(&token_4).model().lookup(ptr2));
    assert!(id(&token_4).model().contains(ptr1));
    assume!(id(r1) ,= id(&token_4).model().lookup(ptr1));
    assert!(id(r1).model() ,= 10.model());
    assert!(id(r2).model() ,= 20.model());
    assert!(id(r3).model() ,= 30.model());
    assert!(false);
}