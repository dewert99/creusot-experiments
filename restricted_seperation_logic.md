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


Raw pointers can be cast to and from references with the following rules
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
`*const` can be treated a `*mut` have the same encoding and `*mut` pointers can be freely cast to `*const` pointers
Note that `std::ptr::addr_of_mut!(x.f)` and `&mut x.f as *mut _` have different semantics and don't return the same pointer.
```rust
#[requires(acc(x, WRITE))]
fn test1(x: *mut (u32, u32)) {
    let y = std::ptr::addr_of_mut!(x.0);
    unsafe{*x = (1, 1)};
    unsafe{*y = 5};
    // All legal since we have permission to x and y (just not separately)
}

#[requires(acc(x, WRITE))]
fn test2(x: *mut (u32, u32)) {
    // Exhaled permission to x when casting to a mutable reference then inhaled permission to y
    let y = &'a mut x.0 as *mut _;
    // sugar for {let t1 = y as &mut _; let t2 = &mut t1.0; let y = t2 as *mut _;}
    // 'a must have ended in order to inhale permission to x again
    unsafe{*x = (1, 1)};
    // 'a must not have ended in order keep permission to y so this is illegal
    // This is also a stacked borrows violation
    unsafe{*y = 5};
}
```

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

### Addresses 
Snapshot/logical equality for pointers uses logical-addresses so `<*const>::address()` is a non-bijectived `#[pure]` function.'
It does have one special property that at any specific time point all pointers with separate positive permission and the same address must be equal.
This allows writing a reference equality function
```rust
#[ensures(result ==> x1 === x2)]
fn address_equal<X>(x1: &X, x2: &X) -> bool {
    let ptr1 = x1 as *const X;
    let ptr2 = x2 as *const X;
    ptr1.address() == ptr2.address() //separate permission to ptr1 and ptr2 means that there equal if there addresses are
    // anonymous lifetime ends and permissions to ptr1 and ptr2 are inhaled
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

#[invariant(acc(self.0) && *self.0 % 2 == 0)]
struct AccPtr(*mut u32);

impl MyTrait for AccPtr {
    fn impure(&self) {
        let ptr = self.0; // pointers are copy
        unsafe{*ptr += 2}; // We have access from the invariant
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
### Possible Solution
Multiply permissions in heap dependent invariants by "surrounding context"
 * Full permission if owned or under mutable reference
 * Arbitrarily small permission if under shared reference
 * `p` if on the heap with permission `p`
We could then add a non heap dependent logical function mapping the snapshots of types with heap dependent invariants
to the footprint of their invariant on the heap.
This way pure/logical functions using these types still won't be heap dependent (unless they have an explicit heap dependent precondition)

As an optimization we could only inhale and exhale invariants when relevant
 * When constructing directly
   * Assume the footprint function of the new object agrees with the heap
   * Exhale invariant (times write permission)
 * When destructuring directly or dropping
   * Inhale invariant (times write permission) 
 * When destructuring a shared reference
   * Inhale invariant (times arbitrarily small permission)
   * Assume the footprint function of the reference agrees with the heap
 * When destructuring a mutable reference
   * Inhale `cur` invariant (times write permission)
   * Assume the footprint function of the `cur` reference agrees with the heap
   * Handle prophecy encoding
 * At the end of the lifetime of a destructured a mutable reference
   * Assume the footprint function of the `fin` reference agrees with the heap
   * Exhale `fin` invariant (times write permission)
 * `acc(t, perm)` where `t: *mut T` contains `t`s invariant times `perm`

 Eg for the above
```rust
trait Invariant {
    #[predicate] // Viper Predicate
    #[ensures(self.inv_pure())]
    fn inv(self) -> bool;

    #[logic] // Viper Function
    fn inv_pure(self) -> bool;
    
    #[logic]
    #[requires(self.inv() * epsion?)] // this is actually heap dependent
    fn assume_footprint(self) -> bool;
}

trait MyTrait {
    fn impure(&self);
    
    #[pure]
    fn pure(&self) -> u32;
}

fn test<X: MyTrait>(x: &X) {
    let val1 = x.pure();
    x.impure();
    let val2 = x.pure();
    assert_eq!(val1, val2); // This holds since x.pure is not heap dependent
}


struct AccPtrInner(*mut u32);

struct AccPtr{data: AccPtrInner, footprint: Heap}

impl<'a, T> Invariant for AccPtr {
    #[predicate] // heap dependent
    #[ensures(self.inv_pure())]
    fn inv(self) -> bool {
        acc(self.data.0) && self.inv_pure()
    }

    #[logic] // not heap dependent
    fn inv_pure(self) -> bool {
        self.footprint[self.data.0] % 2 == 0
    }

    #[logic]
    #[requires(self.inv() * epsion?)] // this is actually heap dependent
    fn assume_footprint(self) -> bool {
        unsafe{*self.data.0 == self.footprint[self.data.0]}
    }
}

impl MyTrait for AccPtr {
    fn impure(&self) {
       inhale!(self.inv() * epsilon?); // before destructure
       assume!(self.assume_footprint()); // before destructure
       let inner = &self.data; // destructures &self
       let ptr = inner.0; 
       unsafe{*ptr += 1}; // FAIL we don't have full permission
    }

    #[pure]
    fn pure(&self) -> u32 { 
       assume!(self.inv_pure()); // before destructure
       let inner = &self.data; // destructures &self
       footprint(self)[inner.0]
    }
}

impl AccPtr {
   #[ensures(fin(self).pure() == cur(self).pure() + 1)]
   fn impure2(&mut self) {
      inhale!(cur(self).inv()); // before destructure
      assume!(cur(self).assume_footprint()); // before destructure
      let inner = &mut self.data; // destructures &mut self
      let ptr = inner.0;
      unsafe{*ptr += 1}; // FAIL we don't have full permission
      assume!(fin(self).assume_footprint()); // before expiry
      exhale!(fin(self).inv()); // before expiry
   }
}

fn bad() {
   let x = 5u32;
   let r = &mut x;
   // casting gives us access
   let y = AccPtr{data: AccPtrInner(r as *mut u32), footprint: havoc()};
   assume!(y.assume_footprint()); // after constructor
   exhale!(y.inv()); // after constructor
   test(&y); // the assertion would fail
   inhale!(y.inv()); // before drop constructor
   assume!(y.assume_footprint()); // before drop
   // r expires but we now have access
}
```
Note: An advantage of this approach is that (program) functions involving types with heap dependent invariants can still be heap independent as long as they don't touch it's fields.
This allows for the encapsulation of separation logic