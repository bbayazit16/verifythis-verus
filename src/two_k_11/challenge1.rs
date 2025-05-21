use vstd::prelude::*;

verus! {

#[allow(unused)]
pub fn max(a: &[i32]) -> (max_idx: usize)
    requires
        0 < a.len() <= usize::MAX,
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[max_idx as int] >= a[i],
{
    let mut x = 0usize;
    let mut y = a.len() - 1;

    while x != y
        invariant
            forall|i: int|
                0 <= i < a.len() && a[i] > a[x as int] && a[i] > a[y as int] ==> x < i < y,
            0 <= x <= y < a.len(),
        decreases y - x,
    {
        if a[x] <= a[y] {
            x += 1;
        } else {
            y -= 1;
        }
    }  // x == y

    x
}

} // verus!
