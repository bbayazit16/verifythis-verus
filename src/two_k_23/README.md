# 2023

## Challenge 1

- Tried with `loop` first, but it was easier to convert the main loop into `while head.is_some()` instead, while that is less idiomatic.
- We automatically 'assume' the following chain:
  - computer memory is finite ==> structs in rust are finite ==> a cell struct can only have finite number of next elements, or is cyclic ==>
    - if cyclic, code works correctly anyways,
    - `Option<Cell>` guarantees that we can always find the end of the chain, on which case the algorithm works.
  - Thus I have skipped specifying 'well-formedness' of the input. But, to do so, you could add a check, saying `cell_len(head)` is less than some constant (such as `usize::MAX`), which automatically ensures the list is terminated, thanks to `Option`.

## Challenge 2

- Only contains tasks 1, 2, and 3.
- Contains two `admit`s:
  - One, axiomatically, to assume that for a HashSet `hashset`, if `hashset.contains(x)`, then `hashset@.contains(x) && hashset.get(x) == Some(x)`
  - Second, a more complex one, but almost axiomatic. Right after inserting into a HashSet in exec mode, it's view mode contains the same element. And, all previous elements are still contained, and their previous properties are reserved. See `fn insert` under `impl Bdd` for more details.
- The library implementation is a direct copy of that seen in OCaml. For that reason, I chose to use `Rc`, and avoid duplication as done in the OCaml code. However, `Rc::ptr_eq` is not supported by the verifier.
  - Key idea: The problem is that we want to verify `Rc::ptr_eq`, but the verifier does not support it.
    We could assign conditionally and assume specification, such as if `ptr_eq(a, b) ==> a =~= b`, which would be true, albeit insufficient for the rest of the challenge. We also want `a =~= b ==> ptr_eq(a, b)`, but how could we know that, when there could be duplicates? So, this code maintains a key invariant, that no duplicates can occur in the hashset, and that making a node preserves that property. To track that, the code 'simulates' a pointer address being assigned in this ghost variable ptr_addresses. The values in the hashmap does not matter, but they're assigned to hashmap length at the moment of assignment.
