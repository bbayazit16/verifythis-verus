# 2016

## Challenge 1
- Uses [Dafny solution](https://verifythis.github.io/onsite/archive/2016/).
- The proof is almost identical to the Dafny solution, except for overflow checks and assumptions.
- I could not get verifier to work properly with 2D array assignments and array initialization. Thus, there are two Rust specification assumptions:
    - `vec![vec![0; n]; n]` correctly produces a 2D array of size `n x n` initialized with 0s.
    - `v[i][j] = value`:
        - Does not change the length of the vector `v`.
        - The length of the nested vectors do not change.
        - Sets the value at `v[i][j]` to `value`.
        - All other indices of `v` remain unchanged.
