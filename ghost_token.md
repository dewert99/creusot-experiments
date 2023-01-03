## Motivation

Safe Rust relies on an aliasing XOR mutability discipline, where mutable references are not allowed to alias with any other reference. This works well for tree shaped data structures but makes it harder to work with data structures with a more general graph shape (eg. doubly linked lists, skip lists, etc.). Rust has certain _safe_ built-in types that allow programmers to work around this restriction by allowing controlled mutation to shared references of these types, but they often involve runtime overhead. The alternative strategy for creating graph-like data structures is to use raw pointers (which can freely alias) in _unsafe_ Rust, but currently the Rust verification tools don't support verifying these types of unsafe operations. `GhostPtrToken` is a way to augment programs using raw pointers so that they can be understood by current verification tools.

## `GhostPtrToken`

`GhostPtrToken` is a ZST (Zero Sized Type) that models the ownership of a collection of raw pointers.
Its specifications are proven in the Rust-Horn-Belt/lambda-rust Coq formalization (THIS STILL NEEDS TO BE DONE!) and can then be used to verify more complex programs using existing tools (Prusti or Creusot).
It is modelled as a finite partial map that maps pointers that it owns to their values on the heap. It supports operations that allow the pointers to be temporarily upgraded to shared or mutable references, but its specifications enforce that it doesn't allow for a mutable reference to alias another reference.


### Vs `GhostCell`
Currently, `GhostPtrToken` enforces that all the pointers it manages are free-able by the global allocator. This allows it to support reasoning about memory-management as well as aliasing (a raw pointer `*mut _` managed by a `GhostPtrToken` can replace a `Rc<RefCell<_>>`). This gives it an advantage over `GhostCell` which would still require handling this at runtime (eg. with reference counting using `Rc<GhostCell<_>>`).  For example a linked-list with a tail pointer implemented using `GhostCell` might look like:
```rust
struct LinkedList<'brand, T>{
	token: GhostToken<'brand>,
	head: Option<Rc<GhostCell<'brand, Node<T>>>>,
	tail: Option<Rc<GhostCell<'brand, Node<T>>>>,
}

struct Node<'brand, T> {
	data: T,
	next: Option<Rc<GhostCell<'brand, Node<T>>>>,
}
```
which would still require the overhead of using reference counting, where one using `GhostPtrToken` would look like.
```rust
struct LinkedList<T>{
	token: GhostPtrToken<T>,
	head: *mut Node<T>,
	tail: *mut Node<T>,
}

struct Node<'brand, T> {
	data: T,
	next: *mut Node<T>,
}
```
which would be just as efficient as what could be created using only raw pointers. Since `GhostCell` wasn't designed for verification, using it may be easier since contracts and invariants are not needed, but it doesn't guarantee functional correctness properties (only memory safety).

### Operations

The primary operations supported by `GhostPtrToken`s are:
- Casting a `Box` into a raw pointer and adding it to the token.
- Removing a raw pointer from the token and casting it back to a box.
```rust
	fn example1(token: &mut GhostPtrToken<u32>) {
		let ptr1: *mut u32 = ptr_from_box(token, Box::new(5));
		// ptr1 points to the value 5, and is managed by token
		let b: Box<u32> = ptr_to_box(token, ptr1);
		// ptr1 is no longer managed by token
		assert!(*b == 5);
	
		// let b2: Box<u32> = ptr_to_box(token, ptr1);
		// this would fail to verify since token longer manages ptr1
		// if this was allowed dropping b and b2 would double free the memory
	}	
```
- Casting a raw pointer contained in the token to a shared reference.
This requires holding a shared reference to the token with the same lifetime which prevents the creation of a non-shared alias.
```rust
	fn example2(token: &mut GhostPtrToken<u32>) {
		let ptr1: *mut u32 = ptr_from_box(token, Box::new(5));
		// ptr1 points to the value 5, and is managed by token
		let r: &u32 = ptr_as_ref(token, ptr1);
		let r2: &u32 = ptr_as_ref(token, ptr1);
		assert_eq!(*r, 5);
		assert_eq!(*r2, 5);
		drop(ptr_to_box(token, ptr1));
	
		// assert!(*r2 == 5);
		// this would fail to borrow check since ptr_to_box takes a mutable reference ending the borrow
		// if this was allowed we would dereference a dangling reference
	
		// assert!(*r == ptr_as_ref(token, ptr1));
		// this would also fail to verify since token longer manages ptr1 
	}	
```
- Casting a raw pointer contained in to token to a mutable reference.
This operation has an unusual signature taking an `&mut &mut GhostPtrToken`,
this allows the inner mutable reference to be used immediately after the call,
but modifies it so it no longer contains the cast pointer until it expires so that it can't be used to create an aliasing mutable reference.
```rust
	#[requires((@*token).contains(ptr1) && (@*token).contains(ptr2)]
	#[requires(ptr1 != ptr2)]
	#[ensures((@^token).contains(ptr1) && (@^token).contains(ptr2)]
	// token will still contain ptr1 and ptr2 when after 'a expires
	fn example3<'a>(token: &'a mut GhostPtrToken<u32>, ptr1: *mut u32, ptr2: *mut u32) 
	-> (&'a mut u32, &'a mut u32){
		let mut token = token;
		let m1: &'a mut u32 = ptr_as_mut(&mut token, ptr1);
		// let m2 = ptr_as_mut(&mut token, ptr1); // Verification error (token no longer contains ptr1)
		let m2: &'a mut u32 = ptr_as_mut(&mut token, ptr2);
		(m1, m2)
	}
```

While it might seem confusing that `token` would still contain `ptr1` and `ptr2` after `'a` expires, even though `ptr_as_mut` seemed to remove them, it can be helpful to consider a less abstract example of this using slices instead of tokens:
```rust
	#[requires((@*slice).len() == 2)]
	#[ensures((@^slice).len() == 2)]
	fn test_slice<'a>(s: &'a mut [u32]) 
	-> (&'a mut u32, &'a mut u32){
		let mut s = s;
		let m1: &'a mut u32 = slice::take_mut(&mut s);
		assert_eq!(s.len(), 1);
		// https://doc.rust-lang.org/std/primitive.slice.html#method.take_mut
		let m2: &'a mut u32 = slice::take_mut(&mut s);
		assert_eq!(s.len(), 0);
		(m1, m2)
		// When 'a expires token contains m1 and m2 again
	}
```
Similarly to how `slice::take_mut` modifies a reference to a slice making it refer to a smaller subsection without modifying the data behind the inner reference.

### Simple example with aliasing
```rust
struct GrandParent<T> {
	child: Box<Parent<T>>,
	grand_child: *mut T,
}

struct Parent<T> {
	child: *mut T,
}

fn example4(token: &mut GhostPtrToken<u32>) {
	let child: *mut u32 = ptr_from_box(token, Box::new(5));
	let parent = Parent{child};
	let grand_parent = GrandParent{child: parent, grand_child: child};
	// grand_parent.child.child and grand_parent.grand_child alias
	
	let mut temp_token = token;
	*ptr_as_mut(grand_parent.child.child, &mut temp_token) += 1;
	// we use a temporary token so that when it expires we'll still have acess to child
	assert_eq!(ptr_as_ref(grand_parent.grand_child, token), 6);
}
```

## Examples using `GhostPtrToken`

### [`LinkedList`](src/linked_list.rs)
A common example of a graph shaped data structure is a singly linked list using a tail pointer, which supports `enqueue`, `dequeue`, `append`, and `iter_mut` operations.

Using separation logic it could be modelled using invariants like:

(Note `∗` is the separating conjunction)

```rust
struct Node<T>{
    data: T,
    next: Ptr<T>,
}

type Ptr<T> = *mut Node<T>;
type Token<T> = GhostToken<Node<T>>;
type TokenM<T> = PMap<Ptr<T>, Node<T>>;

#[predicate]
#[variant(token.len())]
#[ensures(ptr == other ==> result)]
#[ensures(token.contains(ptr) && token.lookup(ptr).next == other ==> result)]
fn lseg<T>(ptr: Ptr<T>, other: Ptr<T>) -> bool {
    ptr == other || (acc(ptr) ∗ lseg(ptr.next, other))
}

pub struct LinkedList<T>{
    head: Ptr<T>,
    tail: Ptr<T>,
}

#[predicate]
pub fn invariant<T>(this: LinkedList<T>) -> bool {
    let LinkedList{head, tail} = this;
    head == ptr::null() || (lseg(head, tail) ∗ acc(tail) ∗ tail.next == ptr::null())
}
```

This separation logic can be extracted by adding a `GhostPtrToken` to the `LinkedList` struct to model the fragment of the heap used in it's invariant. 
Since each call only makes one heap dependent call we can pass the token as an additional parameter and convert `acc(ptr) ∗ X` to `token.contains(ptr) && {let token = token.remove(ptr); X}` to mimic the separating conjunction separating out some permission. Heap independent calls can be easily be handled by converting `g(...) ∗ X` to `g(...) && X` where `g` is heap indepentent.
`lseg` also requires that the token is empty in the base case to help show we are not leaking memory.

```rust
struct Node<T>{
    data: T,
    next: Ptr<T>,
}

type Ptr<T> = *mut Node<T>;
type Token<T> = GhostPtrToken<Node<T>>;
type TokenM<T> = PMap<Ptr<T>, Node<T>>;

#[predicate]
#[variant(token.len())]
#[ensures(ptr == other ==> result)]
#[ensures(token.contains(ptr) && token.lookup(ptr).next == other ==> result)]
fn lseg<T>(ptr: Ptr<T>, other: Ptr<T>, token: TokenM<T>) -> bool {
    if ptr == other {
        token == PMap::empty()
    } else {
        match token.get(ptr) {
            None => false,
            Some(node) => lseg(node.next, other, token.remove(ptr)),
        }
    }
}

pub struct LinkedList<T>{
    head: Ptr<T>,
    tail: Ptr<T>,
    token: Token<T>,
}

#[predicate]
pub fn invariant<T>(this: LinkedList<T>) -> bool {
    let LinkedList{head, tail, token} = this;
    head == ptr::null() || (lseg(head, tail, (@token).remove(tail)) &&
        (@token).contains(tail) && (@token).lookup(tail).next == ptr::null())
}
```


### [`SkipList`](src/skip_list.rs)
Another example of a graph shaped data structure is a skip list.

Unfortunately since `GhostPtrToken`s don't help model concurrency this example will not support concurrent operations. 

Using separation logic the recursive helper for the invariant could be modelled like:

```rust
fn lseg<K>(ptr: Ptr<K>, end: Ptr<K>, level: Int) -> bool {
	if ptr == end {
		true
	} else if level == -1 {
		acc(ptr)
	} else {
		acc(ptr) && (
			((@ptr.nexts).len() > level && (@ptr.nexts)[level] != ptr)
			∗ lseg(ptr, (@ptr.nexts)[level], level - 1)
			∗ lseg((@ptr.nexts)[level], end, level)
		)
	}
}
```

Since it involves two separated recursive call, the extracting the separation logic is somewhat messier. In this type of situation we need to thread the token though the calls so that predicates that used to return `bool` now return `Option<GhostPtrToken>`. `None` is used instead of `false` and `Some(token2)` is used instead of `true` where `token2` is unused remainder of the passed in `token`.  The conversion works similarly to the simpler case, but `f(...) ∗ X` (where `f` is heap dependent) can now be converted to `match f(..., token) {None => None, Some(token) => X}`. While this works it requires extra lemmas to prove the framing of the non-tail recursive call when the part of the token it used didn't change (but the remainder it returned did change). One advantage of this over a tool like Prusti is it can easily deal with the non-separating conjunction by not removing ptr from token in the remaining expression.

```rust
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
```

## Reflection
`GhostPtrToken` works fairly well as a substitute for separation logic, although it might not be as intuitive to use, especially in more complicated cases.  It could potentially be improved by also allowing it (or a variant of it) to support aliasing though cells in order to separately manage different parts of the same allocation.  This version would be more similar to `GhostCell`, with it's only advantage being support of proving functional correctness, and would likely be used in conjunction with the current `GhostPtrToken`.  `GhostPtrToken` also doesn't support atomic operations making it impossible to implement concurrent data structures like concurrent skip-lists. It isn't clear (to me) if `GhostPtrToken` could be extended it this direction. 

## API Reference
```rust
    #[ensures(@result == PMap::empty())]
    pub fn new() -> GhostToken {
        GhostToken(PhantomData)
    }

    /// Takes ownership of all pointers in other by consuming it
    #[ensures((@*this).disjoint(@other))]
    #[ensures((@^this) == (@*this).union(@other))]
    pub fn absorb<T>(this: &mut GhostPtrToken<T>, other: GhostPtrToken<T>) {}

    #[ensures(!(@*t).contains(result))]
    #[ensures(@^t == (@*t).insert(result, *val))]
    pub fn ptr_from_box<T>(val: Box<T>, t: &mut GhostPtrToken<T>) -> *mut T {
        Box::into_raw(val)
    }

    #[requires((@t).contains(ptr))]
    #[ensures(*result == *(@t).lookup(ptr))]
    pub unsafe fn ptr_as_ref<T>(ptr: *mut T, t: &GhostPtrToken<T>) -> &T {
        unsafe {&*ptr}
    }

    // This function takes a double mutable references to allow for two different pointers to viewed as mutable references at the same time
    #[requires((@**t).contains(ptr))]
    #[ensures(*result == *(@**t).lookup(ptr))]
    #[ensures(@*^t == (@**t).remove(ptr))]
    #[ensures(@^*t == (@^^t).insert(ptr, ^result))]
    #[ensures(!(@^^t).contains(ptr))]
    pub unsafe fn ptr_as_mut<'o, 'i, T>(ptr: *mut T, t: &'o mut &'i mut GhostPtrToken<T>) -> &'i mut T {
        unsafe { &mut *ptr}
    }

    #[trusted]
    #[requires((@*t).contains(self))]
    #[ensures(*result == *(@*t).lookup(self))]
    #[ensures((@^t) == (@*t).remove(self))]
    pub unsafe fn ptr_to_box<T>(ptr: *mut T, t: &mut GhostPtrToken<T>) -> Box<T> {
        unsafe { Box::from_raw(ptr) }
    }
```