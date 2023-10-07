# derive-trait
Derive a trait and a delegating impl from an inherent impl block.

## Why go the opposite way?
This macro is designated for single generic types with many small impl blocks
and complex type bounds in each impl block.

- Without a trait, the function user needs to repeat all the type bounds in the impl block
  in every function that requests a type supporting the associated functions.
- Without a macro, the function author needs to write each function signature four times
  (the trait, the inherent impl, the trait impl and delegation)
  and the type bounds twice.
- With the `#[inherent]` macro, the function author would still need to write twice
 (the trait and the trait impl).

Note that use of thsi crate is only advisable for impl blocks with complicated type bounds.
It is not advisable to create single-implementor traits blindly.
