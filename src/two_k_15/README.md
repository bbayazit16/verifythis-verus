# 2015

## Challenge 1
- Translated from [Why3 team's solution](https://toccata.gitlabpages.inria.fr/toccata/gallery/verifythis2015.en.html) directly.
- Filled in some extra proofs for Verus after directly translating from Why3 (e.g, that early return of the algorithm matches the spec; see line 49).
- Note: There are a lot of improvements that can be made to the proof. I believe simplifying array equality (`eq_array`) with forall/subrange/etc, and as a result `spec_is_relaxed_prefix`, and the main loops' invariant are some examples. I missed out on some improvements because I translated directly from the solution.

## Challenge 3
- Taken directly from the [Why3 team's solution](https://toccata.gitlabpages.inria.fr/toccata/gallery/verifythis2015.en.html).
- I believe the proof can be significantly improved (just like Challenge 1), especially with tweaking triggers. The additional lines (compared to the original Why3 team's proof) I added mostly invoke the trigger for `is_list`. 
- The proof performance is not great. With a simple direct translation (without the additional proof block in remove) at the end of `remove`:
```rs
assert(is_list(*l, s)) by {
    assert(forall|k: int| #![trigger s[k]]
        0 <= k < s.len() ==> (Seq::empty().push(i as int) + s)[k + 1] == s[k]);
}
```

the proof is verified in ~10s (Apple M4 Pro, 24GB Ram) with the `--profile` flag. The main bottleneck comes from the nested forall in `s[k] != s[ki]` of `is_list`. With the additional proof block, that is reduced, but I suspect that there could be a better way to write the triggers. So, debugging the triggers with `--profile` might be a good idea.
