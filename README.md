# CaseInsensitiveHashMap

A hashmap for Rust that uses case-insensitive strings as keys.

```rust
let mut map = CaseInsensitiveHashMap::<u8>::new();
map.insert("A", 1);
assert!(map.contains_key("A"));
assert!(map.contains_key("a"));
assert!(!map.contains_key("B"));
assert!(!map.contains_key("Å"));
```

The API is identical to the [HashMap](https://doc.rust-lang.org/std/collections/struct.HashMap.html)
in `std`.

# Implementation

This use the [UniCase](https://crates.io/crates/unicase) crate to handle
the case-insensitivity. Strings that are used as keys are wrapped in
`UniCase` objects so that they hash and compare for equality in a
case-insensitive manner.
