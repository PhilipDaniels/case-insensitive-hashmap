# CaseInsensitiveHashMap

A wrapper around the [std::collections::HashMap](https://doc.rust-lang.org/std/collections/struct.HashMap.html)
that uses case-insensitive Strings for keys.

Since this is a simple wrapper around the standard HashMap,
please see its documentation for more information.

The key type of the CaseInsensitiveHashMap is always `UniCase<String>`.
Most methods that have a key parameter have a constraint `<K: Into<Key>>`.
This means that you can call them with a `String`, a `&str` or a `UniCase<String>`
if you already have one. This make the API more ergonomic than
the alternative of using `UniCase<String>` directly as a key type in your
own `std::collections::HashMap`.

# Examples

```
use unicase::UniCase;
use case_insensitive_hashmap::CaseInsensitiveHashMap;

let mut map = CaseInsensitiveHashMap::new();
map.insert("a", 20);
map.insert("B".to_string(), 40);

// All these are valid key forms.
assert!(map.contains_key("A"));
assert!(map.contains_key("A".to_string()));
let uc = UniCase::new("A".to_string());
assert!(map.contains_key(uc));

// Lookup of values is case-insensitive.
assert_eq!(map.get("a"), Some(&20));
assert_eq!(map.get("A"), Some(&20));

assert_eq!(map["a"], 20);
assert_eq!(map["A"], 20);
```

# Implementation

This uses the [UniCase](https://crates.io/crates/unicase) crate to handle
the case-insensitivity. Strings that are used as keys are wrapped in
`UniCase` objects so that they hash and compare for equality in a
case-insensitive manner.

# Release Notes

- 1.0.1 - bumped version of [UniCase](https://crates.io/crates/unicase) to 2.7.0.
