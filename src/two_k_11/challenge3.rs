use vstd::prelude::*;

verus! {

// Not included in the original Dafny solution; needed in Verus.
// There is a sequence: [a, b, c, ..., f]. Then, there is some element.
// If the sequence contains the element, but that element is not the first, then
// the sequence minus the first element must contain the element.
proof fn lemma_transitive_contains(s: Seq<i32>, x: i32)
    requires
        s.contains(x),
        x != s.first(),
    ensures
        s.drop_first().contains(x),
    decreases s,
{
    // By unfolding the definition of `contains`.
    // There must exist some index, where, s[i] == x, since s.contains(x);
    let index = choose|i: int| 0 <= i < s.len() && s[i] == x;
    // Naturally, s[index] == x.
    // One can, also, `assert(index != 0)`, since x != s.first().
    // Dropping from a sequence => every index shifts by 1. Still contained:
    assert(s.drop_first()[index - 1] == x);
}

proof fn occurrences_concat_transitive(x: i32, s: Seq<i32>, y: i32)
    ensures
        occurrences(Seq::empty().push(x) + s, y) == (if x == y {
            1nat
        } else {
            0
        }) + occurrences(s, y),
    decreases s,
{
    // By induction on s
    if s.len() == 0 {
        reveal_with_fuel(occurrences, 2);
    } else {
        // I.H.
        // Works for n - 1, prove for n;
        occurrences_concat_transitive(x, s.drop_first(), y);

        assert(occurrences(Seq::empty().push(x) + s, y) == (if x == y {
            1nat
        } else {
            0
        }) + occurrences(s, y)) by {
            // [x, <CONCAT S>].drop_first() == [<CONCAT S>] == s
            assert((Seq::empty().push(x) + s).drop_first() == s);
        };
    }
}

// From Dafny solution, with added by compute proof.
// Take a sequence `s` and two values `x`, `y`. The occurences of `y` in s must
// be greater than or equal to s with x removed. Because, x could be equal equal to y, or not.
// In either case, it is greater than or equal.
proof fn occurrences_remove(s: Seq<i32>, x: i32, y: i32)
    ensures
        occurrences(s, y) >= occurrences(remove_spec(s, x), y),
    decreases s,
{
    // By induction on s
    if s.len() == 0 {
        // Base case
    } else {
        // I.H.
        occurrences_remove(s.drop_first(), x, y);

        if s.first() == x {
            // Removed directly
        } else {
            let first_is_y: nat = if s.first() == y {
                1
            } else {
                0
            };

            assert(occurrences(remove_spec(s, x), y) == first_is_y + occurrences(
                remove_spec(s.drop_first(), x),
                y,
            )) by {
                let first_removed = remove_spec(s.drop_first(), x);
                assert(remove_spec(s, x) == Seq::empty().push(s.first()) + first_removed);

                occurrences_concat_transitive(s.first(), first_removed, y);
            };
        }
    }
}

proof fn lemma_drop_first_concat(p: Seq<i32>, q: Seq<i32>)
    requires
        p.len() > 0,
    ensures
        (p + q).drop_first() == p.drop_first() + q,
    decreases p,
{
    assert((p + q).drop_first() == p.drop_first() + q)
}

proof fn lemma_remove_spec_append(p: Seq<i32>, x: i32, a: i32)
    ensures
        remove_spec(p + Seq::empty().push(a), x) =~= remove_spec(p, x) + if a == x {
            Seq::empty()
        } else {
            Seq::empty().push(a)
        },
    decreases p,
{
    // By induction on p.len()
    // Base case
    if p.len() == 0 {
        if a == x {
            assert(remove_spec(Seq::empty().push(a), x) =~= Seq::<i32>::empty()) by {
                reveal_with_fuel(remove_spec, 2);
            };
        } else {
            assert(remove_spec(Seq::empty().push(a), x) == Seq::empty().push(a)) by {
                reveal_with_fuel(remove_spec, 2);
            }
        }
    } else {
        // p.len() >= 1
        // I.H.
        lemma_remove_spec_append(p.drop_first(), x, a);
        lemma_drop_first_concat(p, Seq::empty().push(a));
    }
}

// Proof that removing with prefix is same as removing with take
proof fn lemma_remove_prefix(s: Seq<i32>, x: i32, n: nat)
    requires
        n <= s.len(),
    ensures
        remove_spec(s.take(n as int), x) =~= remove_with_prefix(s, x, n),
    decreases n,
{
    if n == 0 {
    } else {
        lemma_remove_prefix(s, x, (n - 1) as nat);

        let a = s[n - 1];

        assert(s.take(n as int) == s.take((n - 1) as int) + Seq::empty().push(a));
        lemma_remove_spec_append(s.take((n - 1) as int), x, a);
    }
}

// Removing all elements with prefix ==> same as executing remove spec
proof fn lemma_remove_prefix_all_equiv(s: Seq<i32>, x: i32)
    ensures
        remove_spec(s, x) == remove_with_prefix(s, x, s.len()),
{
    lemma_remove_prefix(s, x, s.len());
    assert(s.take(s.len() as int) =~= s);
}

// From dafny team, but modified to use a while loop + invariant directly.
// DO NOT use remove_value directly. This remove fn. removes all occurrences,
// whereas Seq::remove_value removes only one occurrence.
exec fn remove(v: Vec<i32>, x: i32) -> (result: Vec<i32>)
    ensures
        !result@.contains(x),
        v.len() >= result.len(),
        result@ =~= remove_spec(v@, x),
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            result.len() <= i <= v.len(),
            forall|j: int| 0 <= j < result@.len() ==> result@[j as int] != x,
            // result@ =~= remove_spec(v@.take(i as int), x) // doesn't work
            result@ =~= remove_with_prefix(v@, x, i as nat),
        decreases v.len() - i,
    {
        if v[i] != x {
            result.push(v[i]);
        }
        i += 1;
    }

    proof {
        lemma_remove_prefix_all_equiv(v@, x);
    }

    result
}

// Implements s.drop_first() in exec, without assume_specification.
fn first_dropped(v: &Vec<i32>) -> (result: Vec<i32>)
    requires
        v.len() > 0,
    ensures
        v@.drop_first() == result@,
{
    let mut new_v = Vec::new();
    let mut i: usize = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            new_v@ =~= v@.subrange(1, i as int),
        decreases v.len() - i,
    {
        new_v.push(v[i]);
        i += 1;
    }
    new_v
}

// Regular contains implementation, without assume_specification.
fn contains(v: &Vec<i32>, x: i32) -> (found: bool)
    ensures
        found == v@.contains(x),
{
    let mut i: usize = 0;
    let mut result: bool = false;
    while i < v.len() && !result
        invariant
            0 <= i <= v.len(),
            result == exists|j: int| 0 <= j < i && v@[j] == x,
        decreases v.len() - i,
    {
        if v[i] == x {
            result = true;
        }
        i += 1;
    }
    result
}

// ============================================
// ===== Main lemmas/specs from Dafny Team ====
// ============================================
spec fn first_duplicate_spec(s: Seq<i32>) -> i32
    recommends
        has_duplicates(s),
    decreases s,
{
    if s.len() == 0 {
        0
    } else {
        let first = s.first();
        if s.drop_first().contains(first) {
            first
        } else {
            first_duplicate_spec(s.drop_first())
        }
    }
}

spec fn has_duplicates(s: Seq<i32>) -> bool
    decreases s,
{
    if s.len() == 0 {
        false
    } else {
        let first = s.first();
        s.drop_first().contains(first) || has_duplicates(s.drop_first())
    }
}

spec fn occurrences(s: Seq<i32>, x: i32) -> nat
    decreases s,
{
    if s.len() == 0 {
        0
    } else {
        let summand: nat = if s.first() == x {
            1
        } else {
            0
        };
        summand + occurrences(s.drop_first(), x)
    }
}

spec fn remove_spec(s: Seq<i32>, x: i32) -> (removed: Seq<i32>)
    decreases s,
{
    if s.len() == 0 {
        s
    } else {
        if s.first() == x {
            remove_spec(s.drop_first(), x)
        } else {
            Seq::empty().push(s.first()) + remove_spec(s.drop_first(), x)
        }
    }
}

spec fn remove_with_prefix(s: Seq<i32>, x: i32, n: nat) -> Seq<i32>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        remove_with_prefix(s, x, (n - 1) as nat) + if s[n - 1] == x {
            Seq::empty()
        } else {
            Seq::empty().push(s[n - 1])
        }
    }
}

// If a sequence has duplicates => the first duplicate occurs more than once
proof fn multiple_occurences(s: Seq<i32>)
    requires
        has_duplicates(s),
    ensures
        occurrences(s, first_duplicate_spec(s)) > 1,
    decreases s,
{
    if s.drop_first().contains(s.first()) {
        occurrences_when_present(s.drop_first(), s.first());
    } else {
        multiple_occurences(s.drop_first());
    }
}

// From Dafny solution.
proof fn occurrences_when_present(s: Seq<i32>, x: i32)
    requires
        s.contains(x),
    ensures
        occurrences(s, x) > 0,
    decreases s,
{
    if x != s.first() {
        lemma_transitive_contains(s, x);
        occurrences_when_present(s.drop_first(), x);
    }
}

exec fn first_duplicate(s: Vec<i32>) -> (result: i32)
    requires
        has_duplicates(s@),
    ensures
        s@.contains(result),
        result == first_duplicate_spec(s@),
    decreases s.len(),
{
    let first = s[0];
    let rest = first_dropped(&s);
    if contains(&rest, first) {
        first
    } else {
        proof { assert(rest.len() < s.len()) }
        first_duplicate(rest)
    }
}

// Main challenge 3
#[allow(unused)]
fn find_two_duplicates(a: &Vec<i32>) -> (results: (i32, i32))
    requires
        a.len() >= 4,
        has_duplicates(a@),
        has_duplicates(remove_spec(a@, first_duplicate_spec(a@))),
    ensures
        occurrences(a@, results.0) > 1,
        occurrences(a@, results.1) > 1,
        results.0 != results.1,
{
    let x = first_duplicate(a.clone());
    proof {
        multiple_occurences(a@);
    }

    let x_removed = remove(a.clone(), x);

    let y = first_duplicate(x_removed);
    proof {
        multiple_occurences(x_removed@);
        occurrences_remove(a@, x, y);
    }

    (x, y)
}

} // verus!
