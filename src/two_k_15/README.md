# 2015

## Challenge 1
- Translated from [Why3 team's solution](https://toccata.gitlabpages.inria.fr/toccata/gallery/verifythis2015.en.html) directly.
- Filled in some extra proofs for Verus after directly translating from Why3 (e.g, that early return of the algorithm matches the spec; see line 49).
- Note: There are a lot of improvements that can be made to the proof. I believe simplifying array equality (`eq_array`) with forall/subrange/etc, and as a result `spec_is_relaxed_prefix`, and the main loops' invariant are some examples. I missed out on some improvements because I translated directly from the solution.
