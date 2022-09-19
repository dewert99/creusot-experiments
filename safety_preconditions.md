```rust
#[unwinds_when(unw)] //default true
#[requires(pre1)] //default true
#[requires_safety(pre2)] //default true
#[ensures(post1)] //default true
//~^ Could be sugar for #[ensures_always(pre1 ==> post1)]
#[ensures_always(post2)] //default true
```

pre2 ==> (Memory Safety && (Panic1 || Panic2 || post2))
pre1 && pre2 ==> !Panic1 && (Panic2 || post1)
!unw && pre2 ==> Abort || !(Panic1 || Panic2)

can also be written as 

pre2 ==> (Memory Safety && (pre1 ==> !Panic1) && (Abort || (if (Panic1 || Panic2) then unw else (post2 && (pre1 ==> post1)))))

where
Panic1 is "avoidable" panics
Panic2 is "hard to avoid" panic (eg. allocation)

## Updated Resolve
```rust
trait Resolve {
	#[predicate]
	fn resolve(self); // Drop postcondition
	
	#[predicate]
	fn drop_unwinds_when(self); // Also defaults to true
	
	
	// We would probably want to implicitly requires these to be true for arbitrary type parameters unless otherwise stated
	// Related http://aidancully.blogspot.com/2021/12/less-painful-linear-types.html type parameters marked as ?ScopeDrop would not have this have this implicit requirement
	#[predicate]
	fn drop_precondition(self);
	
	#[predicate]
	fn drop_precondition_safety(self);
}
```

## Intrinsic Built-ins
```rust
#[predicate]
fn resolve_rec<X>(x: X);
#[predicate]
fn drop_precondition_rec<X>(x: X);
#[predicate]
fn drop_precondition_safety_rec<X>(x: X);
#[predicate]
fn drop_unwinds_when_rec<X>(x: X);
```

## Drop
```rust
trait Drop {
	#[requires((*self).drop_precondition())]
	#[safety_requires((*self).drop_precondition_safety())]
	#[ensures(drop_precondition_rec(^self)]
	#[ensures_always(drop_precondition_safety_rec(^self)]
	#[ensures_always(resolve_rec(^self) ==> (*self).resolve())]
	#[ensures_always(drop_unwinds_when_rec(^self) ==> (*self).drop_unwinds_when())]
	#[unwinds_when((*self).drop_unwinds_when())]
	fn drop(&mut self);
}
```

## Examples
```rust
#[requires(false)]
#[ensures_always(false)]
fn core::panicking::panic()

#[requires(b)]
#[ensures_always(b)]
#[unwinds_when(!b)]
fn double_check(b: bool) { // Like assert!
  if !b {
    panic!("Assumption failed")
  }
}

#[requires_safety(false)]
fn core::hint::unreachable_unchecked()

#[unwinds_when(false)]
#[requires(false)]
#[ensures_always(false)]
fn core::intrinsics::abort() / std::process::abort()

// keeps default #[unwinds_when(true)]
#[ensures(*result == *val)]
fn std::boxed::Box::<T>::new(val: T)


#[requires(false)] // This is generally bad, but safe
// Skips resolving x 
fn core::mem::forget(x)

#[unwinds_when(x.unwinds_when())]
#[requires(x.precondition())]
#[requires_safety(x.precondition_safety())]
#[ensures_always(x.resolve())]
fn core::mem::drop(x) // This should also automatically be added to locals that go out of scope

#[invariant(x != 0)]
struct HasInvariant {
    x: u32
}

struct DropBomb;

impl Resolve for DropBomb {
    #[predicate]
    fn resolve(self) {false}

    #[predicate]
    fn drop_precondition(self) {false}

    #[predicate]
    fn drop_precondition_safety(self) { true }

    #[predicate]
    fn drop_unwinds_when(self) { true }
}

impl Drop for DropBomb {
    #[requires(false)]
    #[ensures_always(false)]
    fn drop(&mut self) {
        panic!();
    }
}

impl DropBomb {
    #[trusted]
    fn forget(self) {
        std::mem::forget(self);
    }
}

fn eg0(var: &mut HasInvariant) { 
    panic!() // ERROR since we panic even when our precondition holds
}

#[requires(false)]
fn eg1(var: &mut HasInvariant) { 
    panic!() // OK this functions misbehaves but is safe
}

#[requires(false)]
fn eg2(var: &mut HasInvariant) { 
    let x = &mut var.x;
    *x = 0;
    panic!() // ERROR this function is unsafe since it can unwind without the invariant holding
}

#[requires(false)]
fn eg3(var: &mut HasInvariant) {
    let guard = DropBomb; // panics on drop
    let x = &mut var.x;
    *x = 0;
    panic!() // OK gaurd with panic on unwinding which becomes an abort
}

#[safety_requires(false)]
fn eg4(var: &mut HasInvariant) {
    let x = &mut var.x;
    *x = 0;
    panic!(); // OK safety_requires(false) means anything goes
}

fn eg5(var: &mut HasInvariant) {
    let y = Box::new(0); // OK Box::new() may panic but it's a type2 panic so this is ok
}

#[unwinds_when(false)]
fn eg6(var: &mut HasInvariant) {
    let y = Box::new(0); // Error Box::new() may unwind
}

fn eg7(var: &mut HasInvariant) {
    let x = &mut var.x;
    *x = 0;
    let y = Box::new(0); // ERROR this function is unsafe since it can unwind without the invariant holding
    *x = 1;
}

fn eg8(var: &mut HasInvariant) {
    let guard = DropBomb; // panics on drop
    let x = &mut var.x;
    *x = 0;
    let y = Box::new(0);
    *x = 1
    // ERROR dropping guard on the normal path is a type 1 panic
}

#[requires(false)]
fn eg9(var: &mut HasInvariant) {
    let guard = DropBomb; // panics on drop
    let x = &mut var.x;
    *x = 0;
    let y = Box::new(0);
    *x = 1;
    // OK we require(false) and this is safe (also not great for users to work with)
}

fn eg10(var: &mut HasInvariant) {
    let guard = DropBomb; // panics on drop
    let x = &mut var.x;
    *x = 0;
    let y = Box::new(0);
    *x = 1;
    guard.forget(); // takes ownership and forgets guard
    // OK if Box::new panics gaurd causes an abort, otherwise we fix the invariant and forget guard so we don't panic
}



struct DropGuard<'a, T, F: FnMut(&mut T)>{data: &'a mut T, f: F}


impl<'a, T, F> Resolve for DropGuard<'a, T, F> {
	#[predicate]
	fn resolve(self) {self.f.postcondition_mut((self.data,), ())}
	
	#[predicate]
	fn drop_precondition(self) {self.f.precondition((*(self.data),), ())}
	
	#[predicate]
	fn drop_precondition_safety(self) { true }
	
	#[predicate]
	fn drop_unwinds_when(self) { true }
}

impl<'a, T, F> Drop for DropGuard<'a, T, F> {
	#[requires((*self).f.precondition((*((*self).data),), ()))]
	#[ensures_always(*((^self).data) == ^((^self).data) ==> (*self).f.postcondition_mut(((*self).data,), ())]
	fn drop(&mut self) {
		(self.f)(self.data)
	}
}

#[ensures((^var).x == 1)]
#[unwinds_when((^var).x == 2)] // true but we probably wouldn't specify this
fn eg11(var: &mut HasInvariant) {
    let guard = DropGuard{data: &mut var.x, f: |x| {*x = 2;}}; // fixes invariant on drop
    *guard.data = 0;
    let y = Box::new(0); // OK if we unwind the guard's drop will run setting x to 2
    *guard.data = 1;
    guard.f = |x| ();
    // Ok x is now 1 and drop will now do nothing
}
```


All safe functions have/(must have) `#[requires_safety(true)]`
So safe external functions automatically get
```rust
#[unwinds_when(true)]
#[requires(false)]
#[requires_safety(true)]
#[ensures(true)]
#[ensures_safety(true)]
```
While unsafe ones get
```rust
#[unwinds_when(true)]
#[requires(false)]
#[requires_safety(false)]
#[ensures(true)]
#[ensures_safety(true)]
```

## Encoding

```rust
#[unwinds_when(unw)] //default true
#[requires(pre1A)] //default true
#[requires_safety(pre2A)] //default true
#[ensures(post1A)] //default true
#[ensures_always(post2A)] //default true
fn testA(...) -> T{
  ...
}

#[unwinds_when(unw)] //default true
#[requires(pre1B)] //default true
#[requires_safety(pre2B)] //default true
#[ensures(post1B)] //default true
#[ensures_always(post2B)] //default true
fn testB(...) -> T {
  let a = ...;
  testA(...)
}
```
---------------------------------------------->

```rust
#[requires(pre2A && outer_pre ==> pre1A)]
#[ensures(match result {None => uwnA, Some(result) => (post2A && pre1A ==> post1A)})]
fn testA(..., outer_pre: bool) -> Option<T> {
  ...
}

#[requires(pre2B && outer_pre ==> pre1B)]
#[ensures(match result {None => uwnB, Some(result) => (post2B && pre1B ==> post1B)})]
fn testB(..., outer_pre: bool) -> Option<T> {
  let a = ...;
  let res = match testA(..., pre1B) {
	None => {
	  match drop(a, false) { // use false as the outer_pre since we are unwinding anyways
		None => assume false // we abort on double panic (if we wanted to forbid aborts this would be assert false)
		Some(x) => x,
	  };
	  // same for other locals
	  return None
	},
	Some(x) => x
  }
  match drop(a, pre1B) {
	None => {
	  // unwind drop locals that still need dropping
	  return None
	},
	Some(x) => x
  };
  // same for other locals
  return Some(res)
}
```
## trusted and unsafe_trusted
`#[trusted]` should change the last arg of calls (outer_pre) made from pre1 to false
This allows panicking and bad behaviour but not memory unsafety
In a `#[trusted]` functions the `assert!` macro can be used like an `assume` that's runtime checked.

`#[unsafe_trusted]` should be used to completely skip verification


## Safety Invariant Handling
Constructing a type with an invariant asserts the invariant (as a safety precondition)
Functions that destructure a mutable reference to a type with an invariant must reassert the invariant added anytime the lifetime of the destructure ends (even during unwinding)
If the lifetime extends beyond the length of the function then the invariant must be asserted wherever the functions returns (even during unwinding)
All fields (or at least all fields that appear in the invariant) must not be public
The invariant is assumed to hold for any time the type appears


## Safe vs Allow_Unsafe (possible verifications modes)
We could also have to modes safe and allow_unsafe
where everything above is allow_unsafe mode
In safe mode: 
* local variables with a drop_precondition_safety are not allowed
* only requires and ensures clauses are allowed
* types with safety invariant are not allowed to be created or destructured mutably
* trusted functions allow explicit panics (but are otherwise unchanged)
* unsafe_trusted functions are forbidden
* unsafe blocks are forbidden
Crates/Modules in standard mode could call safe functions without requires_safety using the regular requires as the precondition and the conjunction of ensures clauses as the post-condition
Crates/Modules in allow_unsafe mode could call safe functions using the specs as if they were written in allow_unsafe mode