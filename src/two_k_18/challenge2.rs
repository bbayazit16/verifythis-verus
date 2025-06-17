use vstd::prelude::*;

verus! {

spec fn valid_sequence(s: Seq<bool>, n: int) -> bool {
    &&& s.len() == n
    &&& forall|i: int|
        #![trigger s[i]]
        0 <= i < n ==> (s[i] ==> ((i >= 2 && s[i - 2] && s[i - 1]) || (i >= 1 && i < n - 1 && s[i
            - 1] && s[i + 1]) || (i < n - 2 && s[i + 1] && s[i + 2])))
}

spec fn unique_s(s: Seq<Seq<bool>>) -> bool {
    forall|i: int|
        0 <= i < s.len() ==> (forall|j: int|
            0 <= j < s.len() ==> ((#[trigger] s[i]) =~= (#[trigger] s[j]) ==> i == j))
}

spec fn has_false_in_prefix(s: Seq<bool>, k: int) -> bool {
    exists|y: int| 0 <= y < k + 1 && y < s.len() && s[y] == false
}

spec fn find_first_diff_index(left: Seq<bool>, right: Seq<bool>, i: int) -> int
    recommends
        0 <= i <= left.len() && left.len() == right.len(),
    decreases left.len() - i,
{
    if i >= left.len() {
        i
    } else if left[i] != right[i] {
        i
    } else {
        find_first_diff_index(left, right, i + 1)
    }
}

proof fn lemma_find_first_diff_properties(left: Seq<bool>, right: Seq<bool>, i: int)
    requires
        0 <= i <= left.len() && left.len() == right.len(),
    ensures
        forall|j: int| i <= j < find_first_diff_index(left, right, i) ==> left[j] == right[j],
        find_first_diff_index(left, right, i) <= left.len(),
        find_first_diff_index(left, right, i) >= i,
        find_first_diff_index(left, right, i) < left.len() ==> left[find_first_diff_index(
            left,
            right,
            i,
        )] != right[find_first_diff_index(left, right, i)],
    decreases left.len() - i,
{
    if i < left.len() {
        if left[i] == right[i] {
            lemma_find_first_diff_properties(left, right, i + 1);
        }
    }
}

proof fn lemma_uniqueness_prefix(left: Seq<bool>, right: Seq<bool>, prefix: Seq<bool>)
    ensures
        left != right ==> (prefix + left != prefix + right),
{
    if left.len() == right.len() {
        let diff_index = find_first_diff_index(left, right, 0);
        lemma_find_first_diff_properties(left, right, 0);

        if diff_index == left.len() {
            assert(left =~= right);
        } else {
            assert((prefix + left)[diff_index + prefix.len()] != (prefix + right)[diff_index
                + prefix.len()]);
        }
    } else {
        assert((prefix + left).len() != (prefix + right).len());
    }
}

proof fn lemma_existence_of_l(last: Seq<Seq<bool>>, k: int, l: int)
    requires
        0 <= l <= k,
        forall|z: int| #![trigger last[z]] 0 <= z < last.len() ==> 0 <= l < last[z].len(),
        forall|z: int| #![trigger last[z]] 0 <= z < last.len() ==> last[z][l] == false,
    ensures
        forall|z: int| #![trigger last[z]] 0 <= z < last.len() ==> has_false_in_prefix(last[z], k),
{
}

proof fn lemma_uniqueness_implies_unequal_recursive(
    res: Seq<Seq<bool>>,
    j: int,
    prefix: Seq<bool>,
    y: int,
)
    requires
        unique_s(res),
        0 <= j < res.len(),
        0 <= y <= j,
    ensures
        forall|z: int| #![trigger res[z]] 0 <= z < y ==> !((prefix + res[z]) =~= (prefix + res[j])),
    decreases y,
{
    if y > 0 {
        lemma_uniqueness_implies_unequal_recursive(res, j, prefix, y - 1);
        lemma_uniqueness_prefix(res[y - 1], res[j], prefix);
    }
}

proof fn lemma_uniqueness_implies_unequal(res: Seq<Seq<bool>>, j: int, prefix: Seq<bool>)
    requires
        unique_s(res),
        0 <= j < res.len(),
    ensures
        forall|y: int| #![trigger res[y]] 0 <= y < j ==> !((prefix + res[y]) =~= (prefix + res[j])),
{
    lemma_uniqueness_implies_unequal_recursive(res, j, prefix, j);
}

proof fn lemma_unique_add_one(ini: Seq<Seq<bool>>, elm: Seq<bool>)
    requires
        unique_s(ini),
        forall|y: int| #![trigger ini[y]] 0 <= y < ini.len() ==> !(ini[y] =~= elm),
    ensures
        unique_s(ini.push(elm)),
{
}

proof fn lemma_has_false_in_prefix_mono(s: Seq<Seq<bool>>, k: int, k2: int)
    requires
        k2 > k,
        forall|y: int| #![trigger s[y]] 0 <= y < s.len() ==> has_false_in_prefix(s[y], k),
    ensures
        forall|y: int| #![trigger s[y]] 0 <= y < s.len() ==> has_false_in_prefix(s[y], k2),
{
    assert forall|y: int| #![auto] 0 <= y < s.len() implies has_false_in_prefix(s[y], k2) by {
        lemma_hfip_single(s[y], k, k2);
    }
}

proof fn lemma_hfip_single(seq: Seq<bool>, k: int, k2: int)
    requires
        k2 > k,
        has_false_in_prefix(seq, k),
    ensures
        has_false_in_prefix(seq, k2),
{
    assert(exists|y: int| 0 <= y < k2 + 1 && y < seq.len() && seq[y] == false);
}

// `alloc::vec::from_elem` is not supported (note: you may be able to add a Verus specification to this function with `assume_specification`)
// (note: the vstd library provides some specification for the Rust std library, but it is currently limited)
// Therefore, to invoke vec!, we need to use this instead.
#[verifier::external_body]
fn default_vec_with_length<T>(length: usize, default_value: T) -> (result: Vec<T>) where T: Copy
    ensures
        result@.len() == length,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result[i] == default_value,
{
    vec![default_value; length]
}

spec fn v(s: Vec<Vec<bool>>) -> Seq<Seq<bool>> {
    s@.map_values(|ss: Vec<bool>| ss@)
}

spec fn vv(s: Vec<Vec<Vec<bool>>>) -> Seq<Seq<Seq<bool>>> {
    s@.map_values(|ss: Vec<Vec<bool>>| v(ss))
}

spec fn sum(count: Seq<u64>) -> int
    decreases count,
{
    if count.len() == 0 {
        0
    } else {
        count.last() + sum(count.drop_last())
    }
}

#[allow(unused)]
// Can't disable loop isolation, otherwise resource limit is exceeded.
// #[verifier::loop_isolation(false)]
fn count_sequences(i: usize) -> u64
    requires
        4 <= i <= 81,
{
    let mut count = default_vec_with_length(i, 0);
    let mut res: Vec<Vec<Vec<bool>>> = Vec::new();

    count[0] = 1;
    res.push(vec![vec![]]);

    count[1] = 1;
    res.push(vec![vec![false]]);

    count[2] = 1;
    res.push(vec![vec![false, false]]);

    count[3] = 2;
    res.push(vec![vec![false, false, false], vec![true, true, true]]);

    // Verus can verify without these below:
    // proof {
    //     assert(vv(res)[0].len() == (count@[0] as nat));
    //     assert(vv(res)[1].len() == (count@[1] as nat));
    //     assert(vv(res)[2].len() == (count@[2] as nat));
    //     assert(vv(res)[3].len() == (count@[3] as nat));

    //     assert(unique_s(v(res[0])));
    //     assert(unique_s(v(res[1])));
    //     assert(unique_s(v(res[2])));
    //     assert(!(vv(res)[3][0][0] == vv(res)[3][1][0]));
    //     assert(unique_s(v(res[3])));
    // }

    let mut n = 4;
    while n < i
        invariant
            4 <= count@.len() == i <= 81,
            vv(res).len() == (n as int),
            n >= 4,
            // The count length invariant is strictly needed, because
            // Verus can't infer that the length of count won't change. By
            // marking count mutable, we also open it up to changes in length,
            // but we don't change the length as we've already initialized the array
            // in the beginning.
            count@.len() == i,
            forall|j: int| #![trigger vv(res)[j]] 0 <= j < n ==> vv(res)[j].len() == count@[j],
            forall|z: int, y: int|
                #![trigger vv(res)[z][y]]
                0 <= z < n && 0 <= y < vv(res)[z].len() ==> valid_sequence(vv(res)[z][y], z),
            forall|z: int|
                #![trigger vv(res)[z]]
                0 <= z < n ==> unique_s(
                    vv(res)[z],
                ),
        decreases i - n,
    {
        count[n] = count[n - 1];
        let mut last: Vec<Vec<bool>> = Vec::new();

        let mut j = 0;
        while j < res[n - 1].len()
            invariant
                // Invariants because loop isolation: true
                4 <= n < i,
                4 <= count@.len() == i <= 81,
                vv(res).len() == (n as int),
                // Regular invariants
                forall|z: int, y: int|
                    #![trigger vv(res)[z][y]]
                    #![trigger res[z][y]]
                    0 <= z < n && 0 <= y < vv(res)[z].len() ==> valid_sequence(vv(res)[z][y], z),
                count@.len() == i,
                v(last).len() == j,
                0 <= j <= vv(res)[n - 1].len(),
                count@[n as int] =~= count@[n - 1],
                forall|z: int| 0 <= z < vv(res).len() ==> unique_s(#[trigger] vv(res)[z]),
                forall|z: int|
                    0 <= z < j ==> #[trigger] v(last)[z] =~= Seq::empty().push(false) + vv(res)[n
                        - 1][z],
                unique_s(v(last)),
                // Below invariants are true. we don't need them to prove correctness.
                // But, without these below, the resource limit is exceeded:
                forall|z: int| #![auto] 0 <= z < n ==> vv(res)[z].len() == count@[z],
                forall|y: int| #![auto] 0 <= y < j ==> valid_sequence(v(last)[y], n as int),
                forall|z: int| #![auto] 0 <= z < j ==> v(last)[z].len() > 0,
                forall|z: int| #![auto] 0 <= z < j ==> v(last)[z][0] == false,
            decreases res[n - 1].len() - j,
        {
            proof {
                lemma_uniqueness_implies_unequal(v(res[n - 1]), j as int, Seq::empty().push(false));
                assert(forall|y: int|
                    #![trigger v(res[n - 1])[y]]
                    0 <= y < j ==> !((Seq::empty().push(false) + v(res[n - 1])[y]) =~= (
                    Seq::empty().push(false) + v(res[n - 1])[j as int])));

                assert(forall|y: int| #![trigger last[y]] 0 <= y < last.len() ==> {
                    &&& v(last)[y] !~= Seq::empty().push(false) + vv(res)[n - 1][j as int]
                }) by {
                    assert forall|y: int| 0 <= y < last.len() implies 
                        v(last)[y] !~= Seq::empty().push(false) + vv(res)[n - 1][j as int] by {
                        // From lemma_uniqueness_implies_unequal, we get:
                        // res@[n-1]@[y]@ != res@[n-1]@[j]@
                        
                        // Different sequence => different prefixed sequence
                        lemma_uniqueness_prefix(
                            vv(res)[n - 1][y], 
                            vv(res)[n - 1][j as int], 
                            Seq::empty().push(false)
                        );
                    }
                };
            }

            // Extend is not supported
            // This is a 'manual' implementation of extend:
            let mut ext = vec![false];
            let mut z: usize = 0;
            while z < res[n - 1][j].len()
                invariant
                    // Loop isolation: true
                    4 <= n < i == count@.len(),
                    vv(res).len() == (n as int),
                    0 <= j < res[n - 1].len(),
                    // Regular invariants
                    0 <= z <= vv(res)[n - 1][j as int].len(),
                    ext@.len() == z + 1,
                    ext@[0] == false,
                    forall|i: int|
                        1 <= i < ext@.len() ==> ext@[i] == vv(res)[n - 1][j as int][i - 1],
                    ext@ =~= Seq::empty().push(false) + vv(res)[n - 1][j as int].subrange(
                        0,
                        z as int,
                    ),
                decreases res[n - 1][j as int].len() - z,
            {
                ext.push(res[n - 1][j][z]);
                z += 1;
            }

            last.push(ext);

            proof {
                lemma_unique_add_one(
                    v(last).drop_last(),
                    Seq::empty().push(false) + vv(res)[n - 1][j as int],
                );
            }

            j += 1;

        }

        let mut k = 3;
        proof {
            lemma_existence_of_l(v(last), k - 1, 0);
        }

        let mut start_block = vec![true, true, true];

        while k < n
            invariant
                // Invariants needed because loop isolation: true
                vv(res).len() == n,
                4 <= n < i,
                4 <= count@.len() == i <= 83,
                forall|z: int|
                    #![trigger vv(res)[z]]
                    0 <= z < vv(res).len() ==> unique_s(vv(res)[z]),
                k < n ==> 0 <= n - k - 1 < vv(res).len(),
                forall|z: int, y: int|
                    #![trigger vv(res)[z][y]]
                    0 <= z < n && 0 <= y < vv(res)[z].len() ==> vv(res)[z][y].len() == z,
                forall|z: int, y: int|
                    #![trigger vv(res)[z][y]]
                    0 <= z < n && 0 <= y < vv(res)[z].len() ==> valid_sequence(vv(res)[z][y], z),
                // Regular invariants:
                3 <= k <= n && k == start_block@.len(),
                forall|z: int|
                    #![trigger vv(res)[z]]
                    #![trigger count@[z]]
                    0 <= z < n ==> vv(res)[z].len() == count@[z],
                v(last).len() == count@[n as int],
                forall|y: int|
                    #![trigger last[y]]
                    0 <= y < v(last).len() ==> valid_sequence(v(last)[y], n as int),
                forall|y: int| 0 <= y < start_block@.len() ==> start_block@[y],
                forall|z: int|
                    #![trigger last[z]]
                    0 <= z < v(last).len() ==> has_false_in_prefix(v(last)[z], k - 1),
                unique_s(v(last)),
            decreases n - k,
        {
            let mut j = 0;
            let mut nxtblock: Vec<Vec<bool>> = Vec::new();

            while j < res[n - k - 1].len()
                invariant
                    // We need these invariants because loop isolation: true
                    4 <= count@.len() == i <= 83,
                    unique_s(v(last)),
                    unique_s(v(nxtblock)),
                    start_block@.len() == k,
                    0 <= j <= vv(res)[n - k - 1].len(),
                    forall|y: int|
                        0 <= y < vv(res)[n - k - 1].len() ==> (#[trigger] vv(res)[n - k
                            - 1][y]).len() == (n - k - 1),
                    3 <= k < n,
                    n - k - 1 < res.len(),
                    vv(res).len() == n,
                    // Regular invariants:
                    0 <= j <= vv(res)[n - k - 1].len(),
                    forall|z: int| #![auto] 0 <= z < n ==> vv(res)[z].len() == count@[z],
                    v(nxtblock).len() == j,
                    k == start_block@.len() >= 3,
                    forall|y: int| 0 <= y < k ==> start_block@[y],
                    forall|y: int|
                        #![trigger v(nxtblock)[y]]
                        0 <= y < j ==> !has_false_in_prefix(v(nxtblock)[y], k - 1),
                    forall|y: int|
                        #![trigger v(nxtblock)[y]]
                        0 <= y < j ==> has_false_in_prefix(v(nxtblock)[y], k as int),
                    forall|y: int|
                        0 <= y < j ==> v(nxtblock)[y] == (start_block@ + Seq::empty().push(false)
                            + vv(res)[n - k - 1][y]),
                    forall|y: int|
                        0 <= y < vv(res)[n - k - 1].len() ==> valid_sequence(
                            (#[trigger] vv(res)[n - k - 1][y]),
                            (n - k - 1) as int,
                        ),
                    unique_s(vv(res)[n - k - 1]),
                decreases res[n - k - 1].len() - j,
            {
                // Extend is not supported, below is
                // a for loop implementation of extend:
                let mut nxtelm: Vec<bool> = start_block.clone();
                nxtelm.push(false);
                let mut z: usize = 0;
                while z < res[n - k - 1][j].len()
                    invariant
                        // Loop isolation: true, inherited invariants:
                        0 <= n - k - 1 < vv(res).len(),
                        0 <= j < vv(res)[n - k - 1].len(),
                        // Regular invariants:
                        0 <= z <= vv(res)[n - k - 1][j as int].len(),
                        nxtelm@.len() == start_block@.len() + z + 1,
                        nxtelm@ =~= start_block@ + Seq::empty().push(false) + vv(res)[n - k
                            - 1][j as int].subrange(0, z as int),
                    decreases res[n - k - 1][j as int].len() - z,
                {
                    nxtelm.push(res[n - k - 1][j][z]);
                    z += 1;
                }

                // Commented lines are not needed, but I added them during debugging:
                proof {
                    // assert(nxtelm@ =~= start_block@ + Seq::empty().push(false) + vv(res)[n - k - 1][j as int]);
                    lemma_uniqueness_implies_unequal(
                        vv(res)[n - k - 1],
                        j as int,
                        start_block@ + Seq::empty().push(false),
                    );
                    // This assertion is pretty much the main thing Verus can't infer on its own.
                    assert(!nxtelm@[k as int]);

                    // assert(!nxtelm@[k as int]);
                    // assert(has_false_in_prefix(nxtelm@, k as int));
                    lemma_unique_add_one(v(nxtblock), nxtelm@);
                }

                let ghost old_nxtblock = v(nxtblock);
                nxtblock.push(nxtelm);

                proof {
                    // Needed - even though this is clear from extend.
                    // This could be about use of `v`.
                    assert(v(nxtblock) =~= old_nxtblock.push(nxtelm@));
                    assert(forall|y: int|
                        #![auto]
                        0 <= y < j ==> valid_sequence(v(nxtblock)[y], n as int));
                }

                assert(nxtelm@ =~= start_block@ + Seq::empty().push(false) + vv(res)[n - k
                    - 1][j as int]);

                // For debugging, again Verus doesn't need this:
                // assert(start_block.len() + 1 + vv(res)[n - k - 1][j as int].len() == n);

                j += 1;
            }

            // TODO: Remove overflow assumption?
            assume(0 <= count[n as int] + count[n - k - 1] <= u64::MAX);
            count[n] = count[n] + count[n - k - 1];

            // Extend is not supported, again a manual implementation:
            let ghost initial_last = v(last);
            let mut z: usize = 0;
            while z < nxtblock.len()
                invariant
                    0 <= z <= nxtblock.len(),
                    v(last).len() == z + initial_last.len(),
                    v(last) =~= initial_last + v(nxtblock).subrange(0, z as int),
                decreases v(nxtblock).len() - z,
            {
                let cloned = nxtblock[z].clone();
                let ghost old_last = v(last);

                last.push(cloned);
                z += 1;
                proof {
                    assert(v(last) =~= old_last.push(cloned@));
                }
            }

            // True, not needed:
            // assert(v(last).len() == count[n as int]);

            k += 1;

            start_block.push(true);
        }

        // Other true properties:
        // assert(count@.len() == i);
        // assert(v(last).len() == count@[n as int]);

        last.push(start_block);

        // TODO: Remove overflow assumption?
        assume(0 <= count[n as int] + 1 <= u64::MAX);

        count[n] = count[n] + 1;
        n = n + 1;
        res.push(last);
    }

    // Loop invariant:
    // assert(count@.len() == i);

    // Below, these were in the original proof, but not needed in Verus:
    // assert(vv(res)[i - 1].len() == count[i - 1]);
    // assert(
    //     forall|y: int| 0 <= y < vv(res)[i - 1].len() ==> valid_sequence(#[trigger] vv(res)[i - 1][y], i - 1)
    // );
    // assert(unique_s(vv(res)[i - 1]));

    // In case we just want to prove that algorithm correctly computes some direct number,
    // just uncomment below. Make sure to periodically insert assertions (and not just directly compute)!
    // Update: actually, we can't do this, because of a Verus bug
    // (https://github.com/verus-lang/verus/issues/1277), (and #1679, closed as duplicate of #1277)
    // assert(count[4] == 4) by (compute);
    // assert(count[5] == 7) by (compute);
    // assert(count[10] == 72) by (compute);
    // assert(count[15] == 798) by (compute);
    // assert(count[20] == 8855) by (compute);
    // assert(count[30] == 1089155) by (compute);
    // assert(count[35] == 12078909) by (compute);
    // assert(count[40] == 133957148) by (compute);
    // assert(count[45] == 1485607536) by (compute);
    // assert(count[50] == 16475640049) by (compute);
    // assert(count[51] == 26658145586) by (compute);

    count[i - 1]
}

} // verus!
