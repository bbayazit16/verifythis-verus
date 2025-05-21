# 2011

## Challenge 1

- From the [original challenge report](https://verifythis.github.io/onsite/archive/2011/report-cost-competition-2011.pdf), modified the search by elimination code to return `usize` and take a slice of `&[i32]`.
- Challenge specifically states 'non-empty' array, so added `requires a.len() > 0`.
- Added `0 <= x <= y < a.len()` to the invariant to fix overflows.
- Added the assumption that `a.len() <= usize::MAX`.

## Challenge 3

- Taken from Dafny team's solution, translated for Verus.
- Implementations for contains/`s[1..]` without assume_specification.
- Remove all occurrences of `x` from first `n` elements / from all elements, exec, spec and proof.
