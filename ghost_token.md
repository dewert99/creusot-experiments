`GhostPtrToken` is a ZST that models the ownership of a collection of pointers
which allows for types with aliasing pointers to verified using existing tools.
It is modeled by a finite partial map that maps pointers that it owns to their values on the heap.
Currently, it enforces that all the pointers it manages are free-able by the global allocator.

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
A fairly simple singly linked list with a tail pointer, with `enqueue`, `dequeue`, `append`, and `iter_mut`.


The `LinkedList` type and invariant looks something like
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


Note that the `lseg` predicate corresponds roughly to the separation logic predicate:
`ptr == other || (acc(ptr) * lseg(ptr.next, other))`,
but interactions with the heap are managed though the token's model.
The recursive call is passed a reduced version of the token to mimic the separating conjunction.
It also requires that the token is empty in the base case to help show we are not leaking memory.

The fact that predicate only makes one call (or more generally that it only makes tail calls) simplifies things
since we don't need to specifically describe its footprint

### [`SkipList`](src/skip_list.rs)
A simple single threaded skip list with a tail pointer.

Currently, it only has a recursive helper for insert implemented but is designed to support `iter_mut` as well

Since it involves two recursive call, the type invariant helper is somewhat messier
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

This should roughly correspond to the separation logic predicate
```
if ptr == end {
    true
} else if level == -1 {
    acc(ptr)
} else {
    acc(ptr) && (
        ((@ptr.nexts).len() > level) && (@ptr.nexts)[level] != ptr)
        * lseg(ptr, (@ptr.nexts)[level], level - 1)
        * lseg((@ptr.nexts)[level], end, level)
    )
}
```

`lseg` returns the part of the token it didn't use in order to deal with the separating conjunction of two recursive calls.
This way it can require the second recursive call is valid in what's left of the token after the first call.

While this works it requires extra lemmas to prove the framing of the first recursive call when it's part of the token doesn't change.

One advantage of this over a tool like Prusti is it can easily deal with the non-separating conjunction by not removing ptr from token in the future calls.