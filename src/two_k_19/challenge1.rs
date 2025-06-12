use vstd::prelude::*;

verus! {

spec fn ordered(s: Seq<i32>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> s[j] <= s[k]
}

spec fn increasing(s: Seq<i32>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> s[j] < s[k]
}

spec fn decreasing(s: Seq<i32>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> s[j] >= s[k]
}

spec fn monotonic(s: Seq<i32>) -> bool {
    increasing(s) || decreasing(s)
}

spec fn monotonic_cuts(s: Seq<i32>, c: Seq<usize>) -> bool {
    let c_as_seq_i32: Seq<i32> = c.map_values(|element: usize| element as i32);
    increasing(c_as_seq_i32) && c.len() > 0 && (forall|k: int|
        0 <= k < c.len() ==> 0 <= #[trigger] c[k] <= s.len()) && (c[0] == 0 && c[c.len() - 1]
        == s.len()) && (forall|k: int|
        0 < k < c.len() ==> monotonic(s.subrange(c[k - 1] as int, #[trigger] c[k] as int)))
}

spec fn maximal_cuts(s: Seq<i32>, c: Seq<usize>) -> bool {
    monotonic_cuts(s, c) && (forall|k: int|
        0 < k < c.len() - 1 ==> !monotonic(s.subrange(#[trigger] c[k - 1] as int, c[k] + 1)))
}

proof fn extend_cuts(s: Seq<i32>, c: Seq<usize>, d: int)
    requires
        0 <= d < s.len() <= i32::MAX,
        monotonic_cuts(s.subrange(0, d), c),
        monotonic(s.subrange(d, s.len() as int)),
    ensures
        monotonic_cuts(s, c + Seq::empty().push(s.len() as usize)),
{
    let c2 = c + Seq::empty().push(s.len() as usize);

    // Increasing indices
    let c2_as_seq_i32: Seq<i32> = c2.map_values(|element: usize| element as i32);
    assert(increasing(c2_as_seq_i32)) by {
        let c_as_seq_i32: Seq<i32> = c.map_values(|element: usize| element as i32);
        assert forall|j: int, k: int| 0 <= j < k < c2_as_seq_i32.len() implies c2_as_seq_i32[j]
            < c2_as_seq_i32[k] by {
            if k < c2_as_seq_i32.len() - 1 {
                // c is an increasing sequence
                assert(c_as_seq_i32[j] < c_as_seq_i32[k]);
            } else {
                // Removing this causes resource limit to be exceeded
                assert(k == c2_as_seq_i32.len() - 1);
            }
        };
    };

    // All subranges are consecutively monotonic:
    assert forall|k: int| 0 < k < c2.len() implies monotonic(
        s.subrange(c2[k - 1] as int, #[trigger] c2[k] as int),
    ) by {
        if k < c2.len() - 1 {
            assert(s.subrange(0, d).subrange(c[k - 1] as int, c[k] as int) =~= s.subrange(
                c[k - 1] as int,
                c[k] as int,
            )) by {
                assert(c[k - 1] <= c[k]) by {
                    let c_as_seq_i32: Seq<i32> = c.map_values(|element: usize| element as i32);
                    assert(c_as_seq_i32[k - 1] < c_as_seq_i32[k]);
                };
                // The below assertion is not strictly needed, but just helps Verus run faster
                assert(c[k] as int <= s.subrange(0, d).len());
            };
        }
    };
}

proof fn extend_max(s: Seq<i32>, x: int, y: int)
    requires
        0 <= x < y < s.len() <= usize::MAX,
        monotonic(s.subrange(x, y)),
        increasing(s.subrange(x, y)) ==> s[y - 1] >= s[y],
        decreasing(s.subrange(x, y)) ==> s[y - 1] < s[y],
    ensures
        !monotonic(s.subrange(x, y + 1)),
{
    if increasing(s.subrange(x, y)) {
        assert(s.subrange(x, y + 1)[y - 1 - x] == s[y - 1]);
        assert(s.subrange(x, y + 1)[y - x] == s[y]);

        if s.subrange(x, y).len() > 1 {
            // If increasing(s.subrange(x, y)) ==> then s[x] < s[x+1]
            assert(s.subrange(x, y)[0] == s[x]);
            assert(s.subrange(x, y)[1] == s[x + 1]);
            // Now we can use the increasing property
            // By increasing we have:
            // s[x] < s[x + 1]
            // so:
            assert(s.subrange(x, y + 1)[0] == s[x]);
            assert(s.subrange(x, y + 1)[1] == s[x + 1]);
            // Below is not needed, but shows the goal:
            assert(!decreasing(s.subrange(x, y + 1)));
        }
    } else {
        assert(!decreasing(s.subrange(x, y + 1))) by {
            assert(s.subrange(x, y + 1)[y - 1 - x] == s[y - 1]);
            assert(s.subrange(x, y + 1)[y - x] == s[y]);
        }

        // Not decreasing:
        if s.subrange(x, y).len() > 1 {
            // Similar to the proof in the 'if' case at the top
            // If !increasing(s.subrange(x, y)) ==> then s[x] >= s[x+1]
            // (Notice that this is different from decreasing)
            assert(s.subrange(x, y)[0] == s[x]);
            assert(s.subrange(x, y)[1] == s[x + 1]);
            // We have s[x] >= s[x + 1] by !increasing
            // (Notice that this is different from decreasing)
            assert(s.subrange(x, y + 1)[0] == s[x]);
            assert(s.subrange(x, y + 1)[1] == s[x + 1]);
            // Below is not needed, but shows the goal:
            assert(!increasing(s.subrange(x, y + 1)));
        }
    }
}

// For example, here, #[verifier::loop_isolation(false)] causes
// the resource limit to be exceeded. Thus, I have copied over
// the relavant invariants to the inner while loop.
// Challenge 1
#[allow(unused)]
fn monotonic_cutpoints(a: &Vec<i32>) -> (c: Vec<usize>)
    requires
        a@.len() < i32::MAX - 1,
    ensures
        monotonic_cuts(a@, c@),
        maximal_cuts(a@, c@),
{
    let mut c = vec![0];
    let (mut x, mut y) = (0, 1);
    let ghost p = 0int;

    // If stuck trying to prove 'decreases', try assigning a loop variable as ghost,
    // such as `let ghost mut old_y = 0`, keep it lagging behind the loop variable
    // by one execution, and show that at the end of the loop it has decreased.
    while y < a.len()
        invariant
            // We could combine the first three invariants,
            // but combining a lot of invariants gets messy pretty quickly.
            0 <= x < y <= a@.len() + 1 < i32::MAX,
            y == x + 1,
            0 <= p <= x,
            monotonic_cuts(a@.subrange(0, x as int), c@),
            forall|k: int|
                #![trigger c[k]]
                0 < k < c@.len() - 1 ==> !monotonic(a@.subrange(c[k - 1] as int, c[k] + 1)),
            0 < x < a@.len() ==> !monotonic(a@.subrange(p, x + 1)),
            c@.len() > 1 ==> c@[c@.len() - 2] == p,
            // Or, combine with the above invariant using && x > 0
            c@.len() > 1 ==> x > 0,
            // Invariant that is true but not needed / automatically inferred:
            // c@.len() > 0 && c@[0] == 0,
            x == c@[c@.len() - 1] as int,
        // decreases a.len() - y fails! Verus can't prove that a.len() - y terminates,
        // but using the loop invariants such as y == x + 1 and x < y, Verus can
        // automatically prove termination.
        decreases a.len() - x,
    {
        let inc: bool = a[x] < a[y];

        proof {
            // This assertion is important, verus cannot automatically infer this.
            // Also note the use of extensional equality: =~= instead of ==.
            assert(a@.subrange(0, y as int).subrange(0, x as int) =~= a@.subrange(0, x as int));
            extend_cuts(a@.subrange(0, y as int), c@, x as int);
        }

        while y < a.len() && ((a[y - 1] < a[y]) == inc)
            invariant
                // Notice that relavant invariants have been copied over -
                // because we had to disable loop isolation due to resource
                // limits / usage.
                a@.len() < i32::MAX - 1,
                0 <= x < y <= a@.len(),
                monotonic_cuts(a@.subrange(0, x as int), c@),
                monotonic(a@.subrange(x as int, y as int)),
                monotonic_cuts(a@.subrange(0, y as int), c@ + seq![y]),
                inc <==> (a@[x as int] < a@[x + 1]),
                inc ==> increasing(a@.subrange(x as int, y as int)),
                !inc ==> decreasing(a@.subrange(x as int, y as int)),
                y > x + 1 ==> ((a@[y - 2] < a@[y - 1]) <==> inc),
            decreases a.len() - y,
        {
            y += 1;
            proof {
                let old_subrange = a@.subrange(x as int, (y - 1) as int);
                let new_subrange = a@.subrange(x as int, y as int);

                // This is strictly needed, Verus can't infer this.
                // Also, again, note the use of =~=, extensional equality, over ==.
                assert(new_subrange =~= old_subrange + Seq::empty().push(a@[y - 1]));

                if !inc {
                    // An interesting case happens when !inc (not increasing), i.e a[x] >= a[y].
                    // To show that the loop invariant
                    //      !inc ==> decreasing(a@.subrange(x as int, y as int))
                    // holds, we have to manually show the following property,
                    // which asserts that i < j ==> arr[i] >= arr[j],
                    // meaning if the current subrange is not increasing,
                    // then the new (extended) subrange is decreasing
                    assert forall|i: int, j: int|
                        0 <= i < j < new_subrange.len() implies new_subrange[i]
                        >= new_subrange[j] by {
                        if j >= old_subrange.len() && i != old_subrange.len() - 1 {
                            // This is equivalent to the following
                            //      assert(new_subrange[i] == old_subrange[i]);
                            //      assert(old_subrange[i] >= old_subrange[old_subrange.len() - 1]);
                            // But, the vstd::calc macro is also useful for more complex transitive relations.
                            vstd::calc! {
                                (>=)
                                new_subrange[i]; (==) { assert(new_subrange[i] == old_subrange[i]); }
                                old_subrange[i]; (>=) { assert(old_subrange[i] >= old_subrange[old_subrange.len() - 1]); }
                                old_subrange[old_subrange.len() - 1];
                            }
                        }
                    };
                }

                // This is strictly needed, Verus can't infer this.
                // Also, again, note the use of =~=, extensional equality, over ==.

                assert(a@.subrange(0, y as int).subrange(0, x as int) =~= a@.subrange(0, x as int));

                // Everything below is strictly needed, and again notice the
                // use of extensional equality, =~=, over ==.
                let s = a@.subrange(0, y as int);
                assert(s.subrange(x as int, s.len() as int) =~= new_subrange);
                assert(monotonic(s.subrange(x as int, s.len() as int)));
                extend_cuts(s, c@, x as int);
            }
        }
        assert(monotonic(a@.subrange(x as int, y as int)));

        proof {
            if y < a.len() {
                if !inc {
                    // Subrange is not increasing.
                    // But what if we assumed it was increasing, then showed
                    // it can't be, by contradiction?
                    vstd::assert_by_contradiction!(!increasing(a@.subrange(x as int, y as int)), {
                        // At this point, by the macro we have assumed that
                        // increasing(a@.subrange(x as int, y as int))
                        if a@.subrange(x as int, y as int).len() > 1 {
                            // But by increasing assumption we know the following is true:
                            assert(a@.subrange(x as int, y as int)[0] < a@.subrange(x as int, y as int)[1]);
                            // Same element can't be both >= and <, a contradiction
                        }
                    });
                }
                extend_max(a@, x as int, y as int);
            }
        }

        let ghost old_c = c@;
        c.push(y);

        // Why is this needed?
        // Because p is a ghost variable, and assignments to MUTABLE ghost variables
        // (you can always declare ghost variables with `let ghost` in exec mode, just can't
        // mutate them) can't be made in exec mode. So, we go into the proof mode
        // just to mutate p:
        proof {
            p = x as int;
        }

        // To show the invariant holds:
        assert(monotonic_cuts(a@.subrange(0, y as int), c@)) by {
            // As used above, subrange inequality can't be automatically inferred:
            assert(a@.subrange(0, y as int).subrange(0, x as int) =~= a@.subrange(0, x as int));

            // We know the following fact:
            //      assert(old_c =~= c@.subrange(0, c@.len() - 1));

            // This must be explicitly written out, Verus doesn't know this otherwise:
            assert(old_c + Seq::empty().push(y) =~= c@);
        }

        x = y;
        y = x + 1;

        // Bookkeeping properties - not needed, Verus was able to infer the following.
        // These were helpful when debugging:
        // assert(y > x);
        // assert(a.len() - y < a.len() - x);
        // assert(-1 <= a.len() - y);
    }

    if x < a.len() {
        let ghost initial_c = c@;

        c.push(a.len());
        assert(monotonic_cuts(a@, c@)) by {
            // Below, the reasoning is commented out, but Verus
            // can automatically infer the rest. The key point here
            // is using `initial_c` to show the properties of `c@` after extending:
            //  assert(y == a@.len());
            //  assert(monotonic_cuts(a@.subrange(0, y - 1), initial_c));
            //  assert(monotonic_cuts(a@.subrange(0, a@.len() - 1), initial_c));
            let c_new = initial_c + Seq::empty().push(a@.len() as usize);
            // assert(monotonic_cuts(a@, c_new));
            extend_cuts(a@, initial_c, x as int);
            assert(c_new =~= c@);
        }
    }  // else, simple case for assert(monotonic_cuts(a@, c@)), automatically inferred

    proof {
        // Without this, both postconditions fail.
        // Again, this is not an automatic property. It has to be explicitly
        // written.
        // In fact, this property is not even included in vstd::seq_lib::group_seq_properties.
        assert(a@.subrange(0, a@.len() as int) =~= a@);
    }

    c
}

} // verus!
