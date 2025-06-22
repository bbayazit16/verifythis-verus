use vstd::prelude::*;

verus! {

// Without this import, there's only one precondition that fails to upsweep in the main function.
// This could technically be moved to over there to increase the proof performance, but it's better
// to keep this here as it could help with other things when writing new proofs as well.
broadcast use vstd::seq_lib::group_seq_properties;

broadcast proof fn pow2_larger(x: nat)
    ensures
        #[trigger] pow2(x) > x,
    decreases x,
{
    if x == 0 {
        assert(pow2(x) > x) by {
            reveal_with_fuel(pow2, 1);
        };
    } else {
        pow2_larger((x - 1) as nat);
    }
}

// This is here so that we prevent overflows.
spec fn all_sums_bounded(a: Seq<i32>) -> bool {
    forall|i: int, j: int|
        0 <= i < a.len() && 0 <= j < a.len() ==> 0 <= #[trigger] a[i] + #[trigger] a[j] <= i32::MAX
}

spec fn is_pow2(x: nat) -> bool
    decreases x,
{
    if x == 1 {
        true
    } else if x == 0 || x % 2 != 0 {
        false
    } else {
        is_pow2(x / 2)
    }
}

spec fn pow2(x: nat) -> nat
    decreases x,
{
    if x == 0 {
        1
    } else {
        2 * pow2((x - 1) as nat)
    }
}

spec fn div2(x: nat) -> nat {
    x / 2
}

spec fn even(x: nat) -> bool {
    x % 2 == 0
}

spec fn left_most(left: int, right: int) -> int {
    2 * left - right + 1
}

fn div2_impl(x: usize) -> (result: usize)
    ensures
        result == div2(x as nat),
{
    x / 2
}

spec fn sum_range(a: Seq<i32>, start: usize, end: usize) -> i32
    decreases end - start,
{
    if start >= end || start >= a.len() {
        0
    } else {
        (a[start as int] + sum_range(a, (start + 1) as usize, end)) as i32
    }
}

spec fn f(k: nat) -> nat
    decreases k,
{
    if even(k) {
        1
    } else {
        f(div2((k - 1) as nat))
    }
}

// TODO: Prove this.
proof fn f_ensures(k: nat)
    ensures
        f(k) == pow2(min_spec(k)),
        0 < f(k),
        f(k) <= k + 1,
    decreases k,
{
    admit();

    // It's derived from min_spec_ensures, but this cuases resource limit errors:
    // min_spec_ensures(k);
}

// TODO: Prove this.
proof fn min_spec_ensures(k: nat)
    ensures
        0 <= min_spec(k) <= k,
        pow2(min_spec(k) as nat) <= k + 1,
        k % pow2((min_spec(k) + 1) as nat) == pow2(min_spec(k) as nat) - 1,
        forall|z: nat| k as nat % pow2(z + 1) == #[trigger] pow2(z) - 1 ==> z >= min_spec(k),
        min_spec(k) == min_spec(k as nat),
{
    admit();
}

spec fn min_spec(k: nat) -> nat
    decreases k + 1,
{
    // Notice that these two are the same:
    // k % pow2(1) == pow2(0) - 1
    // even(k)
    if k % pow2(1) == pow2(0) - 1 {
        0
    } else {
        1 + min_spec_helper(k, 1)
    }
}

spec fn min_spec_helper(k: nat, n: nat) -> nat
    recommends
        n <= k,
    decreases k + 1 - n,
{
    // Normally n > k should not be here. But, if
    // we don't add || n > k, Verus won't be able to prove
    // the termination, even if we add n <= k in
    // recommends clause.
    if n > k || k % pow2(n + 1) == pow2(n) - 1 {
        0
    } else {
        1 + min_spec_helper(k, n + 1)
    }
}

fn upsweep(a: &mut Vec<i32>, left: usize, right: usize)
    requires
        left < right < old(a).len(),
        all_sums_bounded(old(a)@),
        is_pow2(old(a)@.len()),
        left_most(left as int, right as int) >= 0,
        is_pow2((right - left) as nat),
        !even(right as nat),
        !even(left as nat) || right - left == 1,
    ensures
        a.len() == old(a).len(),
        all_sums_bounded(a@),
        forall|k: nat|
            0 <= k < 2 * (right - left) ==> a[k + left_most(left as int, right as int) as usize]
                == sum_range(
                old(a)@,
                (k as int - f(k as nat) + 1 + left_most(left as int, right as int)) as usize,
                (k as int + 1 + left_most(left as int, right as int)) as usize,
            ),
        0 <= old(a)@[left as int] + old(a)@[right as int] <= i32::MAX,
    decreases right - left + old(a)@.len() + 3,
{
    let space = right - left;
    if space > 1 {
        proof {
            assert(div2(space as nat) == space / 2);
            assert(is_pow2(space as nat));

            if !even(left as nat) {
                assert(!even(left as nat));
                // TODO: Prove the preconditions to upsweep and downsweep:
                admit();
            }
        }

        upsweep(a, left - div2_impl(space), left);
        upsweep(a, right - div2_impl(space), right);
    }
    a[right] = a[left] + a[right];

    proof {
        if space == 1 {
            // TODO: Prove the failing assertion:
            // It's worth using f_ensures.
            //  forall|k: nat| 0 <= k < 2 * (right - left) ==>
            //     a[k + left_most(left as int, right as int) as usize] ==
            //     sum_range(old(a)@,
            //             (k as int - f(k as nat) + 1 + left_most(left as int, right as int)) as usize,
            //             (k as int + 1 + left_most(left as int, right as int)) as usize),
            admit();
        }
    }
}

spec fn bin_weight(i: nat) -> nat
    decreases i,
{
    if i == 0 {
        0
    } else if even(i) {
        bin_weight(div2(i))
    } else {
        1 + bin_weight(div2((i - 1) as nat))
    }
}

fn downsweep(a: &mut Vec<i32>, left: usize, right: usize)
    requires
        left < right < old(a).len(),
        all_sums_bounded(old(a)@),
        is_pow2(old(a)@.len()),
        left_most(left as int, right as int) >= 0,
        is_pow2((right - left) as nat),
        !even(right as nat),
        !even(left as nat) || right - left == 1,
    ensures
        a.len() == old(a).len(),
        all_sums_bounded(a@),
        forall|k: nat|
            left_most(left as int, right as int) <= k <= right ==> a[k as int] == (
            sum_range_bin_weight(
                old(a)@,
                left_most(left as int, right as int) as usize,
                bin_weight((k - left_most(left as int, right as int)) as nat),
            ) + old(a)@[right as int]),
    decreases right - left + old(a)@.len() + 3,
{
    let tmp = a[right];
    a[right] = a[right] + a[left];
    a[left] = tmp;

    let space = right - left;
    if space > 1 {
        proof {
            assert(div2(space as nat) == space / 2);
            assert(is_pow2(space as nat));

            if !even(left as nat) {
                // TODO: Prove this
                admit();
            }
        }

        downsweep(a, left - div2_impl(space), left);
        downsweep(a, right - div2_impl(space), right);
    }
    proof {
        // TODO: Prove this
        admit();
    }
}

spec fn sum_range_bin_weight(a: Seq<i32>, start: usize, count: nat) -> i32
    decreases count,
{
    if count == 0 || start >= a.len() {
        0
    } else {
        (a[start as int] + sum_range_bin_weight(a, (start + 1) as usize, (count - 1) as nat)) as i32
    }
}

// Challenge 2
#[allow(unused)]
fn main_prefix_sum_rec(a: &mut Vec<i32>)
    requires
        is_pow2(old(a)@.len() as nat),
        old(a)@.len() > 1,
        all_sums_bounded(old(a)@),
    ensures
        forall|i: nat| 0 <= i < a.len() ==> a[i as int] == sum_range(old(a)@, 0, i as usize),
{
    let l = div2_impl(a.len()) - 1;
    let r = a.len() - 1;
    proof {
        // These two assertions are needed, otherwise the precondition to upsweep fails:
        assert(r - l == a.len() - div2(a@.len()));
        assert(!even(r as nat));
    }

    upsweep(a, l, r);

    a[r] = 0;

    proof {
        // This assertions is needed, otherwise the precondition to downsweep fails:
        assert(is_pow2((r - l) as nat));
    }

    downsweep(a, l, r);

    proof {
        assert(forall|i: nat| 0 <= i < a.len() ==> a[i as int] == sum_range(old(a)@, 0, i as usize))
            by {
            // TODO: Prove this without admit
            admit();
        }
    }
}

} // verus!
