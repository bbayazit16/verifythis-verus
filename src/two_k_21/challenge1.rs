use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j]
}

// .sort() is not supported - so we must add this. Alternatively, we could
// implement our own sort and prove it correctly sorts, but that deviates
// from the challenge requirements
// Also, assume_specification, as seen below, is hard to get working. assume_specification
// must be defined over the entire function (thus must include generics), but our is_sorted
// function only accepts i32. We could extend is_sorted to take any T, but then we have to restrict
// T to SpecOrd, on which case we get an error:
// 'types are not compatible with this operator (got T/#0 and T/#0)'

// pub assume_specification<T: Ord>[<[T]>::sort](vec: &mut [T])
//     ensures
//         is_sorted(vec@);

#[verifier::external_body]
fn sort(v: &mut Vec<i32>)
    ensures
        old(v)@.to_multiset() =~= v@.to_multiset(),
        is_sorted(v@),
        old(v)@.len() =~= v@.len(),
{
    v.sort();
}

// Challenge is restricted to integer sequences - so we don't have to worry
// about duplicate elements
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
#[allow(unused)]
fn permut(a: &mut Vec<i32>) -> (result: Vec<Vec<i32>>)
    requires
        old(a)@.len() <= i32::MAX,
{
    // Vec::is_empty is not supported!!
    if a.len() == 0 {
        Vec::new()
    } else {
        let mut result: Vec<Vec<i32>> = Vec::new();

        sort(a);
        result.push(a.clone());

        while !next(a).0
            invariant
                a@.len() <= i32::MAX,
        {
            result.push(a.clone());
        }

        result
    }
}

spec fn non_increasing(v: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] >= v[j]
}


// There are solutions to tasks 1, 4, 6.
// Tasks 5 and 2 have partial solutions.
// NOTE: This solutions is a direct translation from VerCors Team Blue's solution
// all ideas and credit for loop invariants goes to them:
// https://github.com/utwente-fmt/vercors/blob/dev/examples/verifythis/2021/TeamBlue/Challenge1.pvl
fn next(a: &mut Vec<i32>) -> (result: (bool, Ghost<int>))
    requires
        old(a)@.len() <= i32::MAX,
    ensures
        !result.0 ==> a@ =~= old(a)@,
        a@.len() =~= old(a)@.len(),
        // Last permutation
        !result.0 ==> forall|i: int, j: int|
            0 <= i <= j < a@.len() - 1 && j == i + 1 ==> a[i] >= a[j],
        // Beginning of the array has not changed
        forall|i: int| 0 <= i < (result.1 as int) < a@.len() ==> old(a)@[i] == a@[i],
        // If there is a result, then it is a valid index
        result.0 ==> 0 <= (result.1 as int) < a@.len(),
        // Smallest changed element increased
        result.0 ==> a@[result.1 as int] > old(a)@[result.1 as int],
        // Elements above smallestChangedIdx were sorted descending
        result.0 ==> forall|k1: int, k2: int|
            (result.1 as int) < k1 <= k2 < a@.len() && k2 == k1 + 1 ==> old(a)@[k1] >= old(
                a,
            )@[k2],
        // Missing part of 5) elements above smallestChangedIdx are in ascending order now
        // THIS FAILS:
        // result.0 ==> forall|j: int, k: int| (result.1 as int) < j <= k < a@.len() - 1 ==> a@[j] <= a@[k],
{
    let mut i = a.len() as i32 - 1;

    while i > 0 && a[(i - 1) as usize] >= a[i as usize]
        invariant
            -1 <= i < a.len(),
            i == -1 ==> a@.len() == 0,
            i >= 0 ==> forall|k1: int, k2: int|
                i <= k1 <= k2 < a@.len() && k2 == k1 + 1 ==> a@[k1] >= a@[k2],
            forall|k: int| 0 <= k < a@.len() ==> a@[k] == old(a)@[k],
            forall|k1: int, k2: int|
                i - 1 < k1 <= k2 < a@.len() && k2 == k1 + 1 ==> old(a)@[k1] >= old(a)@[k2],
            a@ =~= old(a)@,
        decreases i,
    {
        i -= 1;
    }

    if i <= 0 {
        return (false, Ghost(0));
    }

    let mut i: usize = i as usize;

    let mut j = a.len() - 1;
    while a[j] <= a[i - 1]
        invariant
            0 < i < a@.len(),
            forall|k1: int, k2: int| i <= k1 <= k2 < a@.len() && k2 == k1 + 1 ==> a@[k1] >= a@[k2],
            a@[i - 1] < a@[i as int],
            i <= j < a@.len(),
            forall|k: int| 0 <= k < a@.len() ==> a@[k] == old(a)@[k],
            forall|k1: int, k2: int|
                i - 1 < k1 <= k2 < a@.len() && k2 == k1 + 1 ==> old(a)@[k1] >= old(a)@[k2],
            j < a@.len() - 1 ==> a@[j + 1] <= a@[i - 1],
            a@ =~= old(a)@,
        decreases j,
    {
        j -= 1;
    }

    let mut temp = a[i - 1];
    a[i - 1] = a[j];
    a[j] = temp;

    let ghost smallest_changed_index = i - 1;
    j = a.len() - 1;

    while i < j
        invariant
            a@.len() == old(a)@.len(),
            0 <= smallest_changed_index < a@.len(),
            smallest_changed_index < i < a@.len(),
            i - 1 <= j < a@.len(),
            -1 <= (j - i) < a@.len(),
            forall|k: int| 0 <= k < smallest_changed_index ==> a@[k] == old(a)@[k],
            forall|k1: int, k2: int|
                smallest_changed_index < k1 <= k2 < a@.len() && k2 == k1 + 1 ==> old(a)@[k1] >= old(
                    a,
                )@[k2],
            a@[smallest_changed_index] > old(a)@[smallest_changed_index],
        decreases j,
    {
        temp = a[i];
        a[i] = a[j];
        a[j] = temp;

        i += 1;
        j -= 1;
    }

    (true, Ghost(smallest_changed_index))
}

} // verus!
