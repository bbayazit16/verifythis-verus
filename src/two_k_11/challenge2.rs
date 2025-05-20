use vstd::prelude::*;

verus! {

struct Tree {
    val: i32,
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

impl Tree {
    pub closed spec fn maximum(&self) -> int
        decreases self,
    {
        match (&self.left, &self.right) {
            (None, None) => self.val as int,
            (Some(l), None) => vstd::math::max(self.val as int, l.maximum()),
            (None, Some(r)) => vstd::math::max(self.val as int, r.maximum()),
            (Some(l), Some(r)) => vstd::math::max3(self.val as int, l.maximum(), r.maximum()),
        }
    }
}

fn max(a: i32, b: i32) -> (v: i32)
    ensures
        v >= a && v >= b,
        v == a || v == b,
{
    if a >= b {
        a
    } else {
        b
    }
}

#[allow(unused)]
fn tree_max(t: &Tree) -> (max_value: i32)
    ensures
        max_value == t.maximum(),
    decreases t,
{
    match (&t.left, &t.right) {
        (None, None) => t.val,
        (Some(l), None) => max(t.val, tree_max(l)),
        (None, Some(r)) => max(t.val, tree_max(r)),
        (Some(l), Some(r)) => max(t.val, max(tree_max(l), tree_max(r))),
    }
}

} // verus!
