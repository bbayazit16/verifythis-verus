use vstd::prelude::*;

verus! {

// Initially I added generics and did T: PartialOrd to make the
// algorithm generally applicable. But, on element comparison, we get
// the error:
//
// The verifier does not yet support the following Rust
// feature: cmp or arithmetic for non smt arithmetic types
//
// So I have switched to Vec<u32> instead.
struct Sr {
    runs: Vec<usize>,
    data: Vec<u32>,
}

/// 1. Possible indices for runs are always less than or equal to (equal to 
/// in the case of the last index) for the data length.
/// 2. Run indices must be positive
/// 3. All indices of runs must be <= data length
/// 4. Runs must be in increasing order
spec fn correct_run_properties(runs: Seq<usize>, data: Seq<u32>) -> bool {
    &&& runs.len() <= data.len()
    &&& forall|i: int| 0 <= i < runs.len() ==> runs[i] > 0
    &&& forall|i: int| 0 <= i < runs.len() ==> runs[i] <= data.len()
    &&& forall|i: int, j: int| 0 <= i < j < runs.len() ==> runs[i] < runs[j]
    // Last run always points to the last index + 1 (the length)
    // &&& runs.len() > 0 ==> runs[runs.len() - 1] == data.len()
}

// Challenge 2 - merge
#[allow(unused)]
#[verifier::loop_isolation(false)]
fn merge(r_1: &Sr, r_2: &Sr) -> (res: Sr)
    requires
        correct_run_properties(r_1.runs@, r_1.data@),
        correct_run_properties(
            r_2.runs@,
            r_2.data@,
        ),
    ensures
        correct_run_properties(res.runs@, res.data@),
{
    let mut runs: Vec<usize> = Vec::new();
    let mut data: Vec<u32> = Vec::new();

    // From challenge code: di_1 and di_2 are positions in the data array
    let mut di_1 = 0usize;
    let mut di_2 = 0usize;
    // From challenge code: ri_1 and ri_2 are positions in the run array
    let mut ri_1 = 0usize;
    let mut ri_2 = 0usize;

    while ri_1 < r_1.runs.len() || ri_2 < r_2.runs.len()
        // The invariants below may look 'independent', but each are
        // necessary to prove some other invariants. These below are the
        // minimal set of invariants needed, and removing any causes other invariants
        // to fail, or the code to entirely not pass the verification.
        invariant
            // First, the bounds are preserved. Without this, array
            // access indices wouldn't be valid.
            0 <= ri_1 <= r_1.runs@.len(),
            0 <= ri_2 <= r_2.runs@.len(),
            0 <= di_1 <= r_1.data@.len(),
            0 <= di_2 <= r_2.data@.len(),

            // Second, we want the run properties to be preserved.
            correct_run_properties(runs@, data@),
            
            // Third: Notice that the premises are conditions in the while loop.
            // And, notice that the conclusions are the conditions in the nested while
            // loops under this code.
            // What this invariant means, is that if any of this (outer) while loop's
            // conditions hold, then either (or both) nested for loops
            // will execute at least once. This is useful when we want to prove that
            // runs.len() <= data.len() (which itself is a really useful property when
            // wanting to prove array access indices, etc)
            ri_1 < r_1.runs@.len() ==> di_1 < r_1.runs@[ri_1 as int],
            ri_2 < r_2.runs@.len() ==> di_2 < r_2.runs@[ri_2 as int],
            
            // Fourth: This is figured out by simply looking at the inner while loops' code.
            // Whenever we push to data array, we increment either di_1 or di_2 by once.
            // Useful for proving correct_run_properties.
            data@.len() == di_1 + di_2,
        decreases (r_1.runs.len() - ri_1) + (r_2.runs.len() - ri_2),
    {
        let t_1 = ri_1 < r_1.runs.len() && (ri_2 == r_2.runs.len() || r_1.data[di_1] <= r_2.data[di_2]);
    
        let t_2 = ri_2 < r_2.runs.len() && (ri_1 == r_1.runs.len() || r_2.data[di_2] <= r_1.data[di_1]);

        if t_1 {
            while di_1 < r_1.runs[ri_1]
                invariant
                    // We are 'processing the current run'
                    0 <= di_1 <= r_1.runs@[ri_1 as int],
                    // Data length invariant from the outer while loop is preserved
                    data@.len() == di_1 + di_2,
                decreases r_1.runs[ri_1 as int] - di_1,
            {
                data.push(r_1.data[di_1]);
                di_1 += 1;
            }
            ri_1 += 1;
        }
    
        if t_2 {
            while di_2 < r_2.runs[ri_2]
                invariant
                    // We are 'processing the current run'
                    0 <= di_2 <= r_2.runs@[ri_2 as int],
                    // Data length invariant from the outer while loop is preserved
                    data@.len() == di_1 + di_2,
                decreases r_2.runs[ri_2 as int] - di_2,
            {
                data.push(r_2.data[di_2]);
                di_2 += 1;
            }
            ri_2 += 1;
        }

        runs.push(data.len());
    }

    Sr { runs, data }
}

// Challenge 2 - msort
#[verifier::loop_isolation(false)]
#[allow(unused)]
fn msort(a: &Vec<u32>, l: usize, h: usize) -> (result: Sr)
    requires
        l <= h <= a.len(),
    ensures
        correct_run_properties(result.runs@, result.data@),
    decreases
        h - l
{
    if l == h {
        Sr { runs: Vec::new(), data: Vec::new() }
    } else if h - l == 1 {
        Sr { runs: vec![1], data: vec![a[l]] }
    } else {
        let m = l + (h - l) / 2;

        let res_1 = msort(a, l, m);
        let res_2 = msort(a, m, h);

        merge(&res_1, &res_2)
    }
}

} // verus!
