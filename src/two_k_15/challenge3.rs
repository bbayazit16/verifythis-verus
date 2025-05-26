use vstd::prelude::*;

verus! {

pub struct Dll {
    pub prev: Vec<i32>,
    pub next: Vec<i32>,
    #[allow(unused)]
    pub ghost n: int,
}

impl Dll {
    // TODO: annotate with #[verifier::type_invariant]
    pub open spec fn well_formed(&self) -> bool {
        self.prev.len() == self.next.len() == self.n >= 0
    }
}

spec fn valid_in(l: Dll, i: int) -> bool {
    &&& l.well_formed()
    &&& 0 <= i < l.n
    &&& 0 <= l.prev[i] < l.n
    &&& 0 <= l.next[i] < l.n
    &&& l.next[l.prev[i] as int] == i
    &&& l.prev[l.next[i] as int] == i
}

spec fn valid_out(l: Dll, i: int) -> bool {
    &&& l.well_formed()
    &&& 0 <= i < l.n
    &&& 0 <= l.prev[i] < l.n
    &&& 0 <= l.next[i] < l.n
    &&& l.next[l.prev[i] as int] == l.next[i]
    &&& l.prev[l.next[i] as int] == l.prev[i]
}

pub open spec fn is_list(l: Dll, s: Seq<int>) -> bool {
    forall|k: int|
        #![trigger s[k]]
        #![trigger l.prev[s[k]]]
        0 <= k < s.len() ==> (0 <= s[k] < l.n && l.prev[s[k]] == s[if k == 0 {
            s.len() - 1
        } else {
            k - 1
        }] && l.next[s[k]] == s[if k == s.len() - 1 {
            0
        } else {
            k + 1
        }] && (forall|ki: int| 0 <= ki < s.len() ==> k != ki ==> s[k] != s[ki]))
}

// Challenge 3
// See README to better understand why I added the proof at the bottom (I believe the proof
// can be written better)
#[allow(unused)]
exec fn remove(l: &mut Dll, i: i32, Ghost(s): Ghost<Seq<int>>)
    requires
        old(l).well_formed(),
        valid_in(*old(l), i as int),
        is_list(*old(l), Seq::empty().push(i as int) + s),
    ensures
        valid_out(*l, i as int),
        l.well_formed(),
        is_list(*l, s),
{
    l.prev[l.next[i as usize] as usize] = l.prev[i as usize];
    l.next[l.prev[i as usize] as usize] = l.next[i as usize];

    assert(is_list(*l, s)) by {
        let s_cons = Seq::empty().push(i as int) + s;

        if s.len() == 0 {
            // Simple
        } else {  // s.len() > 0
            // rlimit?
            let _ = old(l).prev[i as int];
            let _ = old(l).next[i as int];

            assert(old(l).next[i as int] == s[0]) by {
                assert(s_cons[1] == s[0]);
            }

            assert forall|k: int| #![trigger s[k]] (0 <= k < s.len()) implies ((0 <= s[k] < l.n
                && l.prev[s[k]] == s[if k == 0 {
                s.len() - 1
            } else {
                k - 1
            }] && l.next[s[k]] == s[if k == s.len() - 1 {
                0
            } else {
                k + 1
            }] && (forall|ki: int| 0 <= ki < s.len() ==> k != ki ==> s[k] != s[ki]))) by {
                let current_node = s[k];
                // r limit?
                let _ = s[if k == 0 {
                    s.len() - 1
                } else {
                    k - 1
                }];

                assert forall|ki: int| 0 <= ki < s.len() && k != ki implies current_node
                    != s[ki] by {
                    if (0 <= k < s.len()) {
                        let s_f_k_trigger = (k + 1) as int;
                        let s_f_ki_trigger = (ki + 1) as int;
                        assert(s_cons[(s_f_k_trigger)] != s_cons[s_f_ki_trigger]);
                    }
                }

                assert(old(l).prev[s_cons[(k + 1) as int]] == s_cons[k as int]);
            };
        }
    }

    // Trigger problems? This is the simplest direct translation from the Why3 solution.
    // assert(is_list(*l, s)) by {
    //     assert(forall|k: int| #![trigger s[k]]
    //         0 <= k < s.len() ==> (Seq::empty().push(i as int) + s)[k + 1] == s[k]);
    // }
}

#[allow(unused)]
exec fn put_back(l: &mut Dll, i: i32, Ghost(s): Ghost<Seq<int>>)
    requires
        old(l).well_formed(),
        valid_out(*old(l), i as int),
        is_list(*old(l), s),
        0 < s.len(),
        old(l).next[i as int] == s[0],
        s[0] != i,
    ensures
        l.well_formed(),
        valid_in(*l, i as int),
        is_list(*l, Seq::empty().push(i as int) + s),
{
    l.prev[l.next[i as usize] as usize] = i;
    l.next[l.prev[i as usize] as usize] = i;
}

} // verus!
