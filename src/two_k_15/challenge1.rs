use vstd::prelude::*;

verus! {

spec fn eq_array(a1: Seq<i32>, ofs1: int, a2: Seq<i32>, ofs2: int, len: int) -> bool {
    // a1.subrange(ofs1, ofs1 + len) =~~= a2.subrange(ofs2, ofs2 + len)
    0 <= len && 0 <= ofs1 && 0 <= ofs2 && ofs1 + len <= a1.len() && ofs2 + len <= a2.len()
        && forall|i: int| 0 <= i < len ==> #[trigger] a1[ofs1 + i] == a2[ofs2 + i]
}

spec fn spec_is_relaxed_prefix(pat: Seq<i32>, a: Seq<i32>) -> bool {
    let n = pat.len() as int;
    eq_array(pat, 0, a, 0, n) || exists|i: int|
        0 <= i && i < n && eq_array(pat, 0, a, 0, i) && eq_array(pat, i + 1, a, i, n - i - 1)
}

#[allow(unused)]
exec fn is_relaxed_prefix(pat: &Vec<i32>, a: &Vec<i32>) -> (res: bool)
    requires
        pat.len() <= usize::MAX,
        0 < a.len() <= usize::MAX,
    ensures
        res == spec_is_relaxed_prefix(pat@, a@),
{
    let mut shift: usize = 0;
    let mut ignored: usize = 0;
    let mut i: usize = 0;
    while i < pat.len()
        invariant
            shift == 0 || shift == 1,
            shift == 1 ==> ignored < i,
            a.len() + shift >= i,
            if shift == 0 {
                eq_array(pat@, 0, a@, 0, i as int)
            } else {
                eq_array(pat@, 0, a@, 0, ignored as int) && eq_array(
                    pat@,
                    ignored + 1,
                    a@,
                    ignored as int,
                    (i - ignored - 1),
                ) && !eq_array(pat@, 0, a@, 0, i as int) && (ignored < a.len()
                    ==> pat@[ignored as int] != a@[ignored as int])
            },
        decreases pat.len() - i,
    {
        if i - shift >= a.len() || (pat[i] != a[i - shift]) {
            if shift == 1 {
                proof {
                    assert(spec_is_relaxed_prefix(pat@, a@) == false) by {
                        assert forall|j: int| 0 <= j < pat.len() implies !(eq_array(
                            pat@,
                            0,
                            a@,
                            0,
                            j,
                        ) && eq_array(pat@, j + 1, a@, j, pat.len() as int - j - 1)) by {
                            let ig = ignored as int;
                            let len_check = i - ig;

                            if i - 1 >= a.len() {
                                // simp!
                            } else {
                                let k_fail = len_check - 1;
                                assert(pat@[ig + 1 + k_fail] != a@[ig + k_fail]);
                            }

                            if j <= ig {
                                if eq_array(pat@, 0, a@, 0, j) && eq_array(
                                    pat@,
                                    j + 1,
                                    a@,
                                    j,
                                    pat.len() - j - 1,
                                ) {
                                    assert forall|k_prime: int|
                                        0 <= k_prime < len_check implies #[trigger] pat@[ig + 1
                                        + k_prime] == a@[ig + k_prime] by {
                                        assert(pat@[j + 1 + (ig + k_prime - j)] == a@[j + (ig
                                            + k_prime - j)]);
                                    }
                                }
                            } else {
                                if eq_array(pat@, 0, a@, 0, j) {
                                    if ig < a.len() {
                                        assert(pat@[0 + ig] == a@[0 + ig]);
                                    }
                                }
                            }
                        };
                    };
                }
                return false;
            }
            ignored = i;
            shift = 1;
        }
        i += 1;
    }

    true
}

} // verus!
