# damm

[Damm] check digit generation and validation.

[Damm]: https://en.wikipedia.org/wiki/Damm_algorithm

```rust
extern crate damm;

fn main() {
    assert_eq!(Ok(4), damm::generate(&[5, 7, 2]));
    assert_eq!(Ok(true), damm::validate(&[5, 7, 2, 4]));
}
```
