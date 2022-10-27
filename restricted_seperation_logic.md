## Combining Separation Logic and Prophetic encoding


Basic idea is to always use partial snapshots, up to raw pointers (or UnsafeCell), for types.
The snapshot of a shared reference becomes the underlying type and the snapshot of a mutable reference is a prophetic pair.
Shared and mutable occupy a single heap location which corresponds to their snapshot.

A built-in predicate is to describe access to a heap region:
```rust
#[predicate]
fn acc<T>(ptr: *mut T, perm: Perm) -> bool {
    // built-in
}
```

The `std::ptr::addr_of_mut!` macro can be used to project to subregions of a pointer eg.
```rust
#[requires(acc(x, WRITE))]
#[ensures(acc(result.0, WRITE) && acc(result.1, WRITE))]
#[ensures((*result.0, *result.1) == old(*result))]
fn test(x: *mut (u32, u32)) -> (*mut u32, *mut u32) {
    (std::ptr::addr_of_mut!(x.0), std::ptr::addr_of_mut!(x.1))
}
```
Note that this would work with any positive permission, but not with [no permission](https://doc.rust-lang.org/stable/std/ptr/macro.addr_of_mut.html#:~:text=Note%2C%20however%2C%20that%20the%20expr%20in%20addr_of_mut!(expr)%20is%20still%20subject%20to%20all%20the%20usual%20rules)


Raw pointers can be cast-ed to and from references with the following rules
```rust
#[ensures(acc(result, WRITE) && *result == curr(x))]
#[assert_on_expiry(acc(result, WRITE))]
#[after_expiry(fin(x) == *result)]
fn mut_ref_to_ptr<'a, X>(x: &'a mut X) -> *mut X {
    x as _
}

#[requires(acc(x, WRITE))]
#[ensures(curr(result) == old(*x))]
#[after_expiry(acc(x, WRITE) && *x == fin(result))]
fn mut_ptr_to_ref<'a, X>(x: *mut X) -> &'a mut X {
    x as _
}

#[ensures(acc(result.0, result.1) && *result.0 == curr(x))]
#[assert_on_expiry(acc(result.0, result.1))]
fn ref_to_ptr<'a, X>(x: &'a X) -> (*const X, Perm) {
    x as _
}

#[requires(acc(x, p))]
#[ensures(curr(result) = old(*x))]
#[after_expiry(acc(x, p))]
fn ptr_to_ref<'a, X>(x: *const X, p: Perm) -> &'a X {
    x as _
}
```
Reading and writing raw pointers can be treated as casting them to a short lived reference,
and the reading/writing the reference
`*const` can be treated a `*mut` with that is never allowed full permission

Box functions can also be given specs
```rust
impl Box<T> {
    #[ensures(acc(result, WRITE) && *result == self.deref())]
    fn into_raw(self) -> *mut T;

    #[requires(acc(result, WRITE))]
    fn from_raw(ptr: *mut T) -> Self;
}
```
which allows for an implementation of Box::leak
```rust
#[ensures(curr(result) == x.deref())]
fn leak<X>(x: Box<X>) -> &'static mut X {
    x.into_raw() as _
}
```

### Parametric Framing Problem
If we allow for heap dependent type invariants we run into a framing problem
```rust
trait MyTrait {
    fn impure(&self);
    
    #[pure]
    fn pure(&self) -> u32;
}

fn test<X: MyTrait>(x: &X) {
    let val1 = x.pure();
    x.impure();
    let val2 = x.pure();
    assert_eq!(val1, val2); // We'd probably like this to hold
}

#[invariant(acc(self.0))]
struct AccPtr(*mut u32);

impl MyTrait for AccPtr {
    fn impure(&self) {
        let ptr = self.0; // pointers are copy
        unsafe{*ptr += 1}; // We have access from the invariant
    }

    fn pure(&self) -> u32 {
        unsafe{*self.0} // We have access from the invariant
    }
}

fn bad() {
    let x = 5u32;
    let r = &mut x;
    // casting gives us access
    let y = AccPtr(r as *mut u32);
    test(&y); // the assertion would fail
    // y is dropped exhaling it's invariant
    // r expires but we now have access
}
```