### Motivation

Safe Rust relies on an aliasing XOR mutability discipline where mutable references are not allowed to alias with any other reference. This works well for tree shaped data structures but makes it harder to work with data structure with a more general graph shaped (eg. doubly linked lists, skip lists, etc.). Rust has certain safe built in types that allow programmers to work around this restriction by allowing controlled mutation to shared references of these types, but they often involve runtime overhead. The alternative strategy for creating graph like data structure is to use raw pointers (which can freely alias) and unsafe Rust, but current Rust verification tools don't currently support verifying these types of unsafe operations.

### `GhostPtrToken`

`GhostPtrToken` is a ZST that models the ownership of a collection of raw pointers.
It's specifications are proven in the Rust-Horn-Belt/lambda-rust Coq formalization (THIS STILL NEEDS TO BE DONE!) and can then be used to verify more complex programs using existing tools (Prusti or Creusot).
It is modelled as a finite partial map that maps pointers that it owns to their values on the heap. It supports operations that allow the pointers to be temporarily upgraded to shared or mutable references, but it's specification enforce that it doesn't allow for a mutable reference to alias another reference.
Currently, it enforces that all the pointers it manages are free-able by the global allocator. This allows it to support reasoning about memory-management as well as aliasing (a raw pointer managed by a `GhostPtrToken` can replace a `Rc<RefCell<_>>`), giving it an advantage over `GhostCell` which would still require handling this at runtime (eg. with reference counting using `Rc`).

the API looks something like:
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
    pub fn ptr_from_box_in<T>(val: Box<T>, t: &mut GhostPtrToken<T>) -> *mut T {
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

This separation logic can be extracted by adding a `GhostPtrToken` to the `LinkedList` struct to model the fragment of the heap used in it's invariant. The `lseg` predicate is given an extra parameter representing the fragment of the heap it's allowed to use.
The calls are passed reduced version of the token to mimic the separating conjunction separating out some of the permission. `lseg` also requires that the token is empty in the base case to help show we are not leaking memory.

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

Since it involves two separated recursive call, the extracting the separation logic is somewhat messier. In this case `lseg` returns (a representation of) the remaining portion of the heap that it didn't end up using. This way it can require the second recursive call is valid using only what's left of the token after the first call. While this works it requires extra lemmas to prove the framing of the first recursive call when it's part of the token doesn't change. One advantage of this over a tool like Prusti is it can easily deal with the non-separating conjunction by not removing ptr from token in the future calls.

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