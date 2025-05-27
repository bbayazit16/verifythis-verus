use vstd::prelude::*;

verus! {

spec fn lcp_subarray(a: Seq<i32>, x: int, y: int) -> nat
    decreases a.len() - x, a.len() - y,
{
    if x >= a.len() || y >= a.len() {
        0
    } else if a[x] != a[y] {
        0
    } else {
        1 + lcp_subarray(a, x + 1, y + 1)
    }
}

proof fn lemma_lcp_definition(arr: Seq<i32>, x: int, y: int, l: int)
    requires
        0 <= x <= arr.len(),
        0 <= y <= arr.len(),
        x + l <= arr.len(),
        y + l <= arr.len(),
        l >= 0,
        // Invariant: From KIV solution
        forall|i: int|
            #![trigger arr[x+i]]
            #![trigger arr[y+i]]
            0 <= i < l ==> arr[x + i] == arr[y + i],
        x + l == arr.len() || y + l == arr.len() || arr[x + l] != arr[y + l],
    ensures
        l == lcp_subarray(arr, x, y),
    decreases l,
{
    // By induction on l
    if l == 0 {
        // Vacuous truth: 0 <= i < 0
    } else {
        // Needed for trigger; otherwise arr[x] == arr[y] doesn't work
        assert(arr[x + 0] == arr[y + 0]);

        assert forall|j: int|
            #![trigger arr[x + 1 + j], arr[y + 1 + j]]
            (0 <= j < l - 1) implies arr[x + 1 + j] == arr[y + 1 + j] by {
            if 0 <= j < l - 1 {
                let j_pp_trigger = j + 1;
                assert(arr[x + j_pp_trigger] == arr[y + j_pp_trigger]);
            } // otherwise vacuous
        };

        // I.H.
        lemma_lcp_definition(arr, x + 1, y + 1, l - 1);
    }
}

// Main challenge 1
// #[verifier::loop_isolation(false)]
#[allow(unused)]
fn lcp(arr: &Vec<i32>, x: usize, y: usize) -> (result: u64)
    requires
        arr.len() < usize::MAX,
        x < arr.len() && y < arr.len(),
    ensures
        result == lcp_subarray(arr@, x as int, y as int),
{
    let mut l: usize = 0;
    while (x + l < arr.len() && y + l < arr.len() && arr[x + l] == arr[y + l])
        invariant
            x + l <= arr.len(),
            y + l <= arr.len(),
            forall|i: nat| #![trigger arr[x + i], arr[y + i]] i < l ==> arr@[x + i] == arr@[y + i],
            // l <= arr.len(),
            // Below: from fn - loop isolation properties
            // arr.len() < usize::MAX,
            // x < arr.len() && y < arr.len(),
        decreases arr.len() - l,
    {
        l += 1;
    };

    assert(l == lcp_subarray(arr@, x as int, y as int)) by {
        lemma_lcp_definition(arr@, x as int, y as int, l as int);
    };

    l as u64
}

} // verus!
