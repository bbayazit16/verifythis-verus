# 2023

## Challenge 1
- Tried with `loop` first, but it was easier to convert the main loop into `while head.is_some()` instead, while that is less idiomatic.
- We automatically 'assume' the following chain:
    - computer memory is finite ==> structs in rust are finite ==> a cell struct can only have finite number of next elements, or is cyclic ==>
        - if cyclic, code works correctly anyways,
        - `Option<Cell>` guarantees that we can always find the end of the chain, on which case the algorithm works.
    - Thus I have skipped specifying 'well-formedness' of the input. But, to do so, you could add a check, saying `cell_len(head)` is less than some constant (such as `usize::MAX`), which automatically ensures the list is terminated, thanks to `Option`.