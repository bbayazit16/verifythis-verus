# 2019

## Challenge 1
- Contains Monotonic Segments.
- Solution largely taken from the sample solutions by the organizers. I had to add various additional assertions just to make the same proofs hold in Verus. It was easy to translate from Dafny to Verus, but figuring out the right assertions to help guide Verus was a bit tricky.
- Always remember to assert `assert(a@.subrange(0, a@.len() as int) =~= a@);`.
