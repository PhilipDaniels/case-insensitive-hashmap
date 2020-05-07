# CiHashMap

A hashmap for Rust that uses case-insensitive strings as keys.

```rust
let mut map = CiHashMap::<u8>::new();
map.insert("A", 1);
assert!(map.contains_key("A"));
assert!(map.contains_key("a"));
assert!(!map.contains_key("B"));
assert!(!map.contains_key("Å"));
```


# Implementation

This use the [UniCase](https://crates.io/crates/unicase) crate to handle
the case-insensitivity.

While the API is ergonomic, it's not very efficient, as it
creates new `UniCase` values when you do queries. It would probably
be better to extract the hashing algorithm from UniCase and use
that directly.
