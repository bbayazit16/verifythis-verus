use vstd::prelude::*;

verus! {


/////////// SPEC FUNCTIONS

// even spec is needed for various reasons, independent from the Why3 solution.
// In Verus triggers do not support boolean operators, nor arithmetic operators.
// So, one can't use the expression x % 2 == 0 as a trigger. However, a spec
// function call can be used as a trigger. Of course this comes with a
// drawback: If you accidentally forget that `even` function exists
// and manually use x % 2 == 0, the quantifier won't be instantiated.
// This spec is needed in bodies of quantifiers where there are only
// arithmetic/boolean operators, and the code below tries to use `even`
// everywhere possible.
spec fn even(x: int) -> bool {
    x % 2 == 0
}

// Number of OCCurrences of `x` at `row[start..end]`.
spec fn occ(x: int, row: Seq<i32>, start: int, end: int) -> nat
    decreases end - start,
{
    if start >= end {
        0
    } else {
        (if row[start] == x {
            1nat
        } else {
            0
        }) + occ(x, row, start + 1, end)
    }
}

// Number of Matrix OCCurrences.
// Occurrences of x in `m`, from row 0 to row-1
// and from column 0 to column-1, both inclusive
spec fn mocc(x: int, m: Seq<Vec<i32>>, row: int, column: int) -> int
    decreases row,
{
    if row <= 0 {
        0
    } else {
        occ(x, m[row - 1]@, 0, column) + mocc(x, m, row - 1, column)
    }
}

// If position (i, j) comes before position (k, l) in the matrix
// in the snake order described in Shearsort
// If i < k: true
// Or, if i == k, if i is even, return j < l, otherwise l < j.
spec fn lt(i: int, j: int, k: int, l: int) -> bool {
    i < k || (i == k && if even(i) {
        j < l
    } else {
        l < j
    })
}

// If everything is in snake order in matrix `m`
spec fn snake_order(m: Seq<Vec<i32>>, rows: int, columns: int) -> bool {
    forall|i: int, j: int, k: int, l: int|
        0 <= i < rows && 0 <= j < columns && 0 <= k < rows && 0 <= l < columns && lt(i, j, k, l)
            ==> m[i][j] <= m[k][l]
}

/////////// Bunch of specs for inversions
spec fn inversions(m: Seq<Vec<i32>>, rows: int, columns: int) -> int
    decreases rows, columns, rows, columns,
{
    sum_i(m, rows, columns, 0)
}

spec fn sum_i(m: Seq<Vec<i32>>, rows: int, columns: int, i: int) -> int
    decreases rows - i,
{
    if i >= rows {
        0
    } else {
        sum_j(m, rows, columns, i, 0) + sum_i(m, rows, columns, i + 1)
    }
}

spec fn sum_j(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int) -> int
    decreases columns - j,
{
    if j >= columns {
        0
    } else {
        sum_k(m, rows, columns, i, j, 0) + sum_j(m, rows, columns, i, j + 1)
    }
}

spec fn sum_k(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int) -> int
    decreases rows - k,
{
    if k >= rows {
        0
    } else {
        numof_l(m, rows, columns, i, j, k, 0) + sum_k(m, rows, columns, i, j, k + 1)
    }
}

spec fn numof_l(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int, l: int) -> int
    decreases columns - l,
{
    if l >= columns {
        0
    } else {
        let count: int = if lt(i, j, k, l) && m[i][j] > m[k][l] {
            1
        } else {
            0
        };
        count + numof_l(m, rows, columns, i, j, k, l + 1)
    }
}


// Row sorted?
// Trigger required: otherwise, Verus can't infer triggers automatically
spec fn sorted_row(m: Seq<Vec<i32>>, rows: int, columns: int, row: int, ascending: bool) -> bool {
    0 <= row < rows && m.len() == rows && (forall|i: int|
        0 <= i < rows ==> (#[trigger] m[i]).len() == columns) && if ascending {
        forall|j: int, l: int| 0 <= j <= l < columns ==> m[row][j] <= m[row][l]
    } else {
        forall|j: int, l: int| 0 <= j <= l < columns ==> m[row][j] >= m[row][l]
    }
}

// Column sorted?
// Trigger required: otherwise, Verus can't infer triggers automatically
spec fn sorted_column(m: Seq<Vec<i32>>, rows: int, columns: int, column: int) -> bool {
    0 <= column < columns && m.len() == rows && (forall|i: int|
        0 <= i < rows ==> (#[trigger] m[i]).len() == columns) && forall|i: int, k: int|
        0 <= i <= k < rows ==> (#[trigger] m[i])[column] <= (#[trigger] m[k])[column]
}

/////////// Proof functions - inversions are non-negative

proof fn inv_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int)
    requires
        rows >= 0,
        columns >= 0,
        m.len() == rows,
        forall|i: int| 0 <= i < rows ==> #[trigger] m[i].len() == columns,
    ensures
        inversions(m, rows, columns) >= 0,
{
    sum_i_nonneg(m, rows, columns, 0);
}

proof fn numof_l_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int, l: int)
    requires
        rows >= 0,
        columns >= 0,
        l <= columns,
    ensures
        numof_l(m, rows, columns, i, j, k, l) >= 0,
    decreases columns - l,
{
    // By induction
    if l >= columns {
    } else {
        numof_l_nonneg(m, rows, columns, i, j, k, l + 1);
    }
}

proof fn sum_k_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int)
    requires
        rows >= 0,
        columns >= 0,
        k <= rows,
    ensures
        sum_k(m, rows, columns, i, j, k) >= 0,
    decreases rows - k,
{
    // By induction
    if k >= rows {
    } else {
        numof_l_nonneg(m, rows, columns, i, j, k, 0);
        sum_k_nonneg(m, rows, columns, i, j, k + 1);
    }
}

proof fn sum_j_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int)
    requires
        rows >= 0,
        columns >= 0,
        j <= columns,
    ensures
        sum_j(m, rows, columns, i, j) >= 0,
    decreases columns - j,
{
    // By induction
    if j >= columns {
    } else {
        sum_k_nonneg(m, rows, columns, i, j, 0);
        sum_j_nonneg(m, rows, columns, i, j + 1);
    }
}

proof fn sum_i_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int, i: int)
    requires
        rows >= 0,
        columns >= 0,
        i <= rows,
    ensures
        sum_i(m, rows, columns, i) >= 0,
    decreases rows - i,
{
    // By induction
    if i >= rows {
    } else {
        sum_j_nonneg(m, rows, columns, i, 0);
        sum_i_nonneg(m, rows, columns, i + 1);
    }
}


// External function.
// This function is ONLY required to be implemented for challenge 6.
// So, there is only a specification.
#[allow(unused)]
fn sort_row(m: &mut Vec<Vec<i32>>, rows: usize, columns: usize, row: usize, ascending: bool)
    requires
        0 <= row < rows,
        old(m)@.len() == rows,
        forall|i: int| 0 <= i < rows ==> #[trigger] old(m)[i].len() == columns,
    ensures
        // Other rows are unchanged
        forall|i: int, j: int|
            0 <= i < rows && 0 <= j < columns && i != row ==> m[i][j] == old(m)[i][j],
        // Occurrences are the same
        forall|x: int|
            mocc(x, m@, rows as int, columns as int) == mocc(
                x,
                old(m)@,
                rows as int,
                columns as int,
            ),
        // Row is sorted
        sorted_row(m@, rows as int, columns as int, row as int, ascending),
        // Inversions do not increase
        inversions(m@, rows as int, columns as int) <= inversions(
            old(m)@,
            rows as int,
            columns as int,
        ),
        // Matrix dimensions preserved
        m.len() == rows,
        forall|i: int| 0 <= i < rows ==> #[trigger] m[i].len() == columns,
{
    external_fn()
}

// External function.
// This function is ONLY required to be implemented for challenge 6.
// So, there is only a specification.
#[allow(unused)]
fn sort_column(m: &mut Vec<Vec<i32>>, rows: usize, columns: usize, column: usize) -> (nochange: bool)
    requires
        0 <= column < columns,
        old(m)@.len() == rows,
        forall|i: int| 0 <= i < rows ==> #[trigger] old(m)[i].len() == columns,
    ensures
        // Other rows are unchanged
        forall|i: int, j: int|
            0 <= i < rows && 0 <= j < columns && j != column ==> m[i][j] == old(m)[i][j],
        // Previously sorted columns are still sorted
        forall|c: int| 0 <= c < columns && c != column && sorted_column(old(m)@, rows as int, columns as int, c) ==> 
            sorted_column(m@, rows as int, columns as int, c),
        // Occurrences are the same
        forall|x: int|
            mocc(x, m@, rows as int, columns as int) == mocc(
                x,
                old(m)@,
                rows as int,
                columns as int,
            ),
        // No change condition
        nochange ==> forall|i: int|
            0 <= i < rows ==> (#[trigger] m[i])[column as int] == old(m)[i][column as int],
        // Column is sorted
        sorted_column(m@, rows as int, columns as int, column as int),
        // Inversions do not increase
        inversions(m@, rows as int, columns as int) <= inversions(
            old(m)@,
            rows as int,
            columns as int,
        ),
        // Strict decrease when changed
        !nochange ==> inversions(m@, rows as int, columns as int) < inversions(
            old(m)@,
            rows as int,
            columns as int,
        ),
        // Matrix dimensions preserved
        m.len() == rows,
        forall|i: int| 0 <= i < rows ==> (#[trigger] m[i]).len() == columns,
{
    external_fn()
}

//// Previous overflow proofs that are no longer needed,
/// after refactoring with while true loop. I will still
/// leave these below, in case they're needed:
// spec fn log2n_plus_1_spec(n: int) -> int {
//     vstd::arithmetic::logarithm::log(2, n) + 1
// }

// proof fn lemma_log2n_plus_1_gt_0(n: int)
//     requires
//         n >= 0
//     ensures
//         log2n_plus_1_spec(n) > 0
// {
//     vstd::arithmetic::logarithm::lemma_log_nonnegative(2, n);
// }

// #[verifier::external_body]
// fn log2n_plus_1(n: usize) -> (result: usize)
//     ensures
//         result == log2n_plus_1_spec(n as int) >= 0
// {
//     n.ilog2() as usize
// }

//// Main challenge
// Challenge 3
#[allow(unused)]
fn shearsort(n: usize, m: &mut Vec<Vec<i32>>)
    requires
        0 <= n <= usize::MAX,
        old(m).len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] old(m)[i].len() == n,
    ensures
        // task 2
        forall|x: int| mocc(x, m@, n as int, n as int) == mocc(x, old(m)@, n as int, n as int),
        // task 3
        snake_order(m@, n as int, n as int),
{
    // Normally, the loop should be bounded by iter_count < log2n_plus_1(n).
    // Thus, the solution would be:
    // let mut iter_count: usize = 0;
    // proof { 
    //     // To prove the before-iteration of the loop invariant 
    //     // iter_count <= log2n_plus_1_spec(n as int)
    //     lemma_log2n_plus_1_gt_0(n as int)
    // };

    loop
        invariant
            forall|x: int| #[trigger]
                mocc(x, m@, n as int, n as int) == #[trigger] mocc(x, old(m)@, n as int, n as int),
            m.len() == n,
            // Trigger needed - Verus can't infer trigger automatically
            forall|i: int| 0 <= i < n ==> #[trigger] m[i].len() == n,
            // and, for the bounded solution: iter_count <= log2n_plus_1_spec(n as int),
        decreases inversions(m@, n as int, n as int)
        // again, for the bounded solution: decreases log2n_plus_1_spec(n as int) - iter_count,
    {
        let ghost l1_inv = inversions(m@, n as int, n as int);

        for i in 0..n
            invariant
                forall|k: int|
                    // Trigger needed - Verus can't infer trigger automatically
                    // Example reason why even(...) is needed as opposed to k % 2 == 0.
                    0 <= k < i ==> sorted_row(m@, n as int, n as int, k, #[trigger] even(k)),
                forall|x: int| #[trigger]
                    mocc(x, m@, n as int, n as int) == #[trigger] mocc(
                        x,
                        old(m)@,
                        n as int,
                        n as int,
                    ),
                inversions(m@, n as int, n as int) <= l1_inv,
                m.len() == n,
                // Important point:
                // Here, for example, trigger for m[j], as opposed to m[j].len(), is
                // strictly needed. Otherwise, the last invariant of the next
                // for loop fails. A solution could be to either modify
                // the trigger as I did (setting it to m[j]), or manually invoke
                // the trigger.
                //
                // Below, notice the paranthesized trigger syntax (where appropriate):
                // Normally, doing #[trigger] m[j].len() would mean that the quantifier
                // should be instantiated with j on a call m[j].len()
                // On the contrary, (#[trigger] m[j]).len() means the quantifier should
                // be instantiated on m[j] instead.
                forall|j: int| 0 <= j < n ==> (#[trigger] m[j]).len() == n,
        {
            sort_row(m, n, n, i, i % 2 == 0);
        }

        let ghost l2_m = m@;
        let ghost l2_inv = inversions(m@, n as int, n as int);
        let mut nochange = true;

        for j in 0..n
            invariant
                nochange ==> forall|i: int, j: int|
                    0 <= i < n && 0 <= j < n ==> #[trigger] m[i][j] == l2_m[i][j],
                forall|l: int| 0 <= l < j ==> #[trigger] sorted_column(m@, n as int, n as int, l),
                forall|x: int| #[trigger]
                    mocc(x, m@, n as int, n as int) == #[trigger] mocc(
                        x,
                        old(m)@,
                        n as int,
                        n as int,
                    ),
                inversions(m@, n as int, n as int) <= l2_inv,
                !nochange ==> inversions(m@, n as int, n as int) < l2_inv,
                m@.len() == n,
                forall|k: int| 0 <= k < n ==> #[trigger] m[k]@.len() == n,
        {
            let nch = sort_column(m, n, n, j);
            if !nch {
                nochange = false;
            }
        }

        if nochange {
            proof {
                lemma_sorted_snake_order(m@, n as int);
            }
            return;
        }

        proof {
            // The assertion below is not needed - but it was something
            // I added to debug, because `decreases` was not satisfied at the end.
            // The proof inv_nonneg, however, is strictly needed here.
            // Otherwise, verifier would think that the inversions
            // decrease to -infinity. We have to show that decreases
            // clause is bounded below, and indeed decreases.

            // assert(inversions(m@, n as int, n as int) < l1_inv);
            inv_nonneg(m@, n as int, n as int);
        }
    }
    // This point is never reached. In fact, here you could do assert(false)
    // and the verifier would still accept - because the verifier knows
    // that for {} (infinite) loop can't be exited without return/break.
}

proof fn lemma_sorted_snake_order(m: Seq<Vec<i32>>, n: int)
    requires
        m.len() == n >= 0,
        forall|i: int| 0 <= i < n ==> #[trigger] m[i].len() == n,
        forall|k: int| 0 <= k < n ==> sorted_row(m, n, n, k, #[trigger] even(k)),
        forall|l: int| 0 <= l < n ==> sorted_column(m, n, n, l),
    ensures
        snake_order(m, n, n),
{
    assert forall|i: int, j: int, k: int, l: int|
        0 <= i < n && 0 <= j < n && 0 <= k < n && 0 <= l < n && lt(i, j, k, l)
        implies m[i][j] <= m[k][l]
    by {
        // The case when i == k (same row) is simple,
        // and verus can automatically prove the case.
        if i != k {
            // Different rows, i < k
            // Verus can infer: assert(i < k);
            if j == l {
                // Same column, different rows
                // Sufficient to use the fact that column is sorted
                assert(sorted_column(m, n, n, j));
            } else if j < l {
                if even(i) {
                    // Verus can infer: assert(m[i][j] <= m[i][l]);
                    assert(sorted_column(m, n, n, l));
                } else {
                    // m[i][j] <= m[k][j]
                    assert(sorted_column(m, n, n, j));
                    
                    if !even(k) {
                        if i + 1 < n {
                            // assert(even(i + 1)) is needed here,
                            // verus can't infer that automatically
                            assert(even(i + 1));
                            assert(sorted_row(m, n, n, i + 1, true));
                        }
                    }
                }
            } else {
                // j > l
                if even(i) {
                    assert(sorted_column(m, n, n, j));
                    if even(k) {
                        if i + 1 < n {
                            // i is even, i + 1 is odd
                            // This assertion is needed - verus can't infer this automatically
                            assert(!even(i + 1));
                            assert(m[i][j] <= m[i + 1][j]);
                            
                            assert(sorted_column(m, n, n, l));
                        }
                    }
                }
            }
        }
    }
}

// Remainder from previous solution: Attempt to bound by n * n.
// We must assert this property by (nonlinear_arith)
// Otherwise, Verus can't reason about nonlinear properties such as n * n
// (whereas it could reason with things like n * 3, refactoring it as addition.)
// Notice the additional requires: without it, by (nonlinear_arith) does not
// inherit outer context, since it is a specialized solver.
// assert(n * n <= usize::MAX) by (nonlinear_arith) requires 0 <= n <= u16::MAX;

// For sort-row and sort-column
#[verifier::external_body]
fn external_fn<A>() -> (x: A)
    ensures
        false,
{
    unimplemented!();
}

} // verus!
