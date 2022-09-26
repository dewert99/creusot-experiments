## Prusti syntax to Creusot syntax
Basic version doesn't support de-referencing mutable references that aren't either a parameter or result
```
'a := Arbitrary Lifetime
'c := Lifetime of the call
exp := Rust Expression
exp_ref := Rust Expresion with type &_
field := Rust Field
pat := Rust Pattern
lit := Rust Literal
id := Rust Identifier
param<'a> := one of the parameters that has type &'a mut _
result := the result keyword when the return type is &'r mut _
'r := the lifetime of result 

f := Rust Function (Assume methods calls have already been desugared)
ts := old | curr | after_expiry<'r> | before_expiry<'r>
(Time slice)


#[requires(exp)] => #[cruesot_requires(at_ts(old, exp))]
#[ensures(exp)] => #[creusot_ensures(at_ts(curr, exp))]
#[after_expiry(exp)] => #[creusot_ensures(at_ts(after_expiry<'r>, exp))]

at_ts: ts, exp -> cruesot_exp | Compile Error

at_ts(ts, old(exp)) => at_ts(old, exp)
at_ts(after_expiry<'r>, before_expiry(exp)) => at_ts(before_expiry<'r>, exp)]
at_ts(ts, before_expiry(exp)) => Compile Error
// Constructors can be though of like functions
at_ts(ts, f(exp...)) => f(at_ts(ts, exp)...)
at_ts(ts, exp.field) => at_ts(ts, exp).field 
// note getting a field from a mutable refererence should be desugared to (*exp).field
at_ts(ts, match exp1 {(pats => exps)...}) => match at_ts(ts, exp) {(pats => at_ts(ts, exps) ...)}
// If and let can be thougt of like match
as_tes(ts, lit) => lit
at_ts(ts, *exp_ref) => *at_rs(exp_ref)
// Note coercing a mutable reference to a shared reference counts as derefrencing
at_ts(old, *param<'a>) => *param
at_ts(curr, *result) => *result
at_ts(curr, *param<'c>) => ^param
at_ts(after_expiry<'r>, *param<'r>) => ^param
at_ts(before_expiry<'r>, *result) => ^result
at_ts(ts, *exp) => Compile Error
as_tes(ts, id) => id
```

Somewhat more advanced version
```


'a := Arbitrary Lifetime
'c := Lifetime of the call
exp := Rust Expression
exp_ref := Rust Expresion with type &_
exp_mut<'a> := Rust Expresion with type &'a mut _
pearlite_exp := Pearlite Expression
pearlite_exp_mut<'a> := Pearlite Expresion with type &'a mut _
field := Rust Field
pat := Rust Pattern
lit := Rust Literal
id := Rust Identifier

f := Rust Function (Assume methods calls have already been desugared)
ts := old | curr | after_expiry<'a> | before_expiry<'a>
(Time slice)


#[requires(exp)] => #[cruesot_requires(at_ts(old, exp))]
#[ensures(exp)] => #[creusot_ensures(at_ts(curr, exp))]
#[after_expiry<'a>(exp)] => #[creusot_ensures(at_ts(after_expiry<'a>, exp))]

at_ts: ts, exp -> pearlite_exp | Compile Error

at_ts(ts, old(exp)) => at_ts(old, exp)
at_ts(after_expiry<'a>, before_expiry(exp)) => at_ts(before_expiry<'a>, exp)]
at_ts(ts, before_expiry(exp)) => Compile Error
at_ts(ts, f(exp...)) => f(at_ts(ts, exp)...)
at_ts(ts, exp.field) => at_ts(ts, exp).field 
at_ts(ts, match exp1 {(pats => exps)...}) => match at_ts(ts, exp) {(pats => at_ts(ts, exps) ...)}
as_tes(ts, lit) => lit
at_ts(ts, *exp_ref) => *at_rs(exp_ref)
as_ts(ts, *exp_ref) => deref_at_ts(ts, at_ts(ts, exp_ref))
as_ts(ts, id) => id

polarity: pearlite_exp -> set polarity

polarity(lit) -> {}
polarity(param) -> {Consume}
polarity(result) -> {Produce}
polarity(id) -> //polarity of the type id was bound to
polarity(pearlite_exp.field) -> polarity(pearlite_exp)
polarity(ts, match exp1 {(pats => exps)...}) => union(polarity(exps...))
polarity(*pearlite_exp) -> polarity(pearlite_exp)
polarity(^pearlite_exp) -> !polarity(pearlite_exp) // Elementwise flip
polarity(f(pearlite_exp...)) -> {Produce, Consume} // This could also be improved by inlining and/or paramatricity tricks

deref_at_ts: ts, pearlite_exp_mut, polarity? -> pearlite_exp | Compile Error

deref_at_ts(old, pearlite_exp_mut) => deref_at_ts(old, pearlite_exp_mut, polarity(pearlite_exp_mut))
deref_at_ts(old, pearlite_exp_mut<'a>, {Consume}) => *pearlite_exp_mut
deref_at_ts(curr, pearlite_exp_mut<'a>, {Produce}) => *pearlite_exp_mut  where polarity(pearlite_exp_mut) == Consume
deref_at_ts(curr, pearlite_exp_mut<'c>, {Consume}) => ^pearlite_exp_mut
deref_at_ts(after_expiry<'a>, *pearlite_exp_mut<'a>, {Consume}) => ^pearlite_exp_mut
deref_at_ts(before_expiry<'a>, *pearlite_exp_mut<'a>, {Produce}) => ^pearlite_exp_mut
deref_at_ts(ts, *exp, polarity) => Compile Error
```
Note: Even in this version doesn't support mutable de-referencing within pure/logical functions 
## Examples
Assume we can determine `last` and `unwrap` preserve polarity
```rust
#[requires(vec1.last() != None)]
#[requires(*vec1.last().unwrap() < 100)]
#[ensures(*vec2.last().unwrap() == 1 + old(*vec1.last().unwrap()))]
#[after_expiry<'a>(*old(vec1.last().unwrap()) == before_exiry(*curr(vec2.last().unwrap)))] // Note this needs new syntax `curr`
fn test<'c, 'a>(vec1: &'c mut Vec<&'a mut u32>, vec2: &'c mut Vec<&'a mut u32>) {
    let x = vec1.pop().unwrap();
    *x += 1;
    vec2.push(x)
}
```
```
at_ts(curr, *unwrap(last(*vec2)) == 1 + old(*unwrap(last(1vec2))))
at_ts(curr, *unwrap(last(*vec2))) == at_ts(1) + at_ts(curr, old(*unwrap(last(*vec1))))
at_ts_deref(curr, at_ts(curr, unwrap(last(*vec2)))) == 1 + at_ts(old, *unwrap(last(*vec1)))
at_ts_deref(curr, unwrap(last(at_ts(curr, *vec2)))) == 1 + at_ts_deref(old, at_ts(old, unwrap(last(*vec1))))
at_ts_deref(curr, unwrap(last(at_ts_deref(curr, at_ts(curr, vec1))))) == 1 + at_ts_deref(old, unwrap(last(at_ts(old, *vec1))))
at_ts_deref(curr, unwrap(last(at_ts_deref(curr, vec2)))) == 1 + at_ts_deref(old, unwrap(last(at_ts_deref(old, at_ts(old, vec1)))))
at_ts_deref(curr, unwrap(last(at_ts_deref(curr, vec2, polarity(vec2))))) == 1 + at_ts_deref(old, unwrap(last(at_ts_deref(old, vec1))))
at_ts_deref(curr, unwrap(last(at_ts_deref(curr, vec2, {Consume})))) == 1 + at_ts_deref(old, unwrap(last(at_ts_deref(old, vec1, polarity(vec1)))))
at_ts_deref(curr, unwrap(last(^vec2)) == 1 + at_ts_deref(old, unwrap(last(at_ts_deref(old, vec1, {Consume}))))
at_ts_deref(curr, unwrap(last(^vec2)), polarity(unwrap(last(^vec2)))) == 1 + at_ts_deref(old, unwrap(last(*vec1)))
at_ts_deref(curr, unwrap(last(^vec2)), polarity(^vec2)) == 1 + at_ts_deref(old, unwrap(last(*vec1)), polarity(unwrap(last(*vec1))))
at_ts_deref(curr, unwrap(last(^vec2)), !polarity(vec2)) == 1 + at_ts_deref(old, unwrap(last(*vec1)), polarity(*vec1))
at_ts_deref(curr, unwrap(last(^vec2)), !{Consume}) == 1 + at_ts_deref(old, unwrap(last(*vec1)), polarity(vec1))
at_ts_deref(curr, unwrap(last(^vec2)), {Produce}) == 1 + at_ts_deref(old, unwrap(last(*vec1)), {Consume})
*unwrap(last(^vec2)) == 1 + *unwrap(last(*vec1))
```
```
at_ts(after_expiry<'a>, *old(unwrap(last(*vec1))) == before_exiry(*curr(unwrap(last(*vec2)))))
at_ts(after_expiry<'a>, *old(unwrap(last(*vec1)))) == at_ts(after_expiry<'a>, before_exiry(*curr(unwrap(last(*vec2)))))
at_ts(after_expiry<'a>, *old(unwrap(last(*vec1)))) == at_ts(before_expiry<'a>, *curr(unwrap(last(*vec2))))
at_ts_deref(after_expiry<'a>, at_ts(after_expiry<'a>, old(unwrap(last(*vec1))))) == at_ts_deref(before_expiry<'a>, at_ts(before_expiry<'a>, curr(unwrap(last(*vec2)))))
at_ts_deref(after_expiry<'a>, at_ts(old, unwrap(last(*vec1)))) == at_ts_deref(before_expiry<'a>, at_ts(curr, unwrap(last(*vec2))))
at_ts_deref(after_expiry<'a>, unwrap(last(at_ts(old, *vec1)))) == at_ts_deref(before_expiry<'a>, unwrap(last(at_ts(curr, *vec2))))
at_ts_deref(after_expiry<'a>, unwrap(last(at_ts_deref(old, at_ts(old, vec1))))) == at_ts_deref(before_expiry<'a>, unwrap(last(at_ts_deref(curr, at_ts(curr, vec2)))))
at_ts_deref(after_expiry<'a>, unwrap(last(at_ts_deref(old, vec1)))) == at_ts_deref(before_expiry<'a>, unwrap(last(at_ts_deref(curr, vec2))))
at_ts_deref(after_expiry<'a>, unwrap(last(at_ts_deref(old, vec1, polarity(vec1))))) == at_ts_deref(before_expiry<'a>, unwrap(last(at_ts_deref(curr, vec2, polarity(vec2)))))
at_ts_deref(after_expiry<'a>, unwrap(last(at_ts_deref(old, vec1, {Consume})))) == at_ts_deref(before_expiry<'a>, unwrap(last(at_ts_deref(curr, vec2, {Consume}))))
at_ts_deref(after_expiry<'a>, unwrap(last(*vec1))) == at_ts_deref(before_expiry<'a>, unwrap(last(^vec2)))
at_ts_deref(after_expiry<'a>, unwrap(last(*vec1)), polarity(unwrap(last(*vec1)))) == at_ts_deref(before_expiry<'a>, unwrap(last(^vec2)), polarity(unwrap(last(^vec2))))
at_ts_deref(after_expiry<'a>, unwrap(last(*vec1)), polarity(*vec1)) == at_ts_deref(before_expiry<'a>, unwrap(last(^vec2)), polarity(^vec2))
at_ts_deref(after_expiry<'a>, unwrap(last(*vec1)), polarity(vec1)) == at_ts_deref(before_expiry<'a>, unwrap(last(^vec2)), !polarity(vec2))
at_ts_deref(after_expiry<'a>, unwrap(last(*vec1)), {Consume}) == at_ts_deref(before_expiry<'a>, unwrap(last(^vec2)), !{Consume})
at_ts_deref(after_expiry<'a>, unwrap(last(*vec1)), {Consume}) == at_ts_deref(before_expiry<'a>, unwrap(last(^vec2)), {Produce})
^unwrap(last(*vec1)) == ^unwrap(last(^vec2))
```
Note: This would still would fail with something like
```rust
#[ensures(*(if b {arg} else {result}) == 5)]
fn test<'a, 'c>(arg: &'c mut u32, borrow: &'a mut u32, b: bool) -> &'a u32 {
    *(if b {arg} else {borrow}) = 5;
    borrow
}
```
The translation would be
```
at_ts(curr, *(if b {arg} else {result}) == 5)
at_ts(curr, *(if b {arg} else {result})) == at_ts(curr, 5)
at_ts_deref(curr, at_ts(curr, if b {arg} else {result})) == 5
at_ts_deref(curr, if at_ts(curr, b) {at_ts(arg, b)} else {at_ts(curr, result)}) == 5
at_ts_deref(curr, if b {arg} else {result}) == 5
at_ts_deref(curr, if b {arg} else {result}, polarity(if b {arg} else {result})) == 5
at_ts_deref(curr, if b {arg} else {result}, union(polarity(arg), polarity(result)) == 5
at_ts_deref(curr, if b {arg} else {result}, union({Produce}, {Consume})) == 5
Complile Error
```