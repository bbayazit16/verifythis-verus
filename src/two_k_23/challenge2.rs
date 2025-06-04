#![allow(unused)]

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    rc::Rc,
};

use vstd::prelude::*;

verus! {

type BddMap = HashSet<Rc<Node>>;

struct Bdd {
    values: BddMap,
    // We want to verify `Rc::ptr_eq`, but the verifier does not support it.
    // We could assign conditionally and assume specification, such as if
    // ptr_eq(a, b) ==> a =~= b, which would be true, albeit insufficient for the rest of the challenge.
    // We also want a =~= b ==> ptr_eq(a, b), but how could we know that, when
    // there could be duplicates? So, this code maintains a key invariant, that
    // no duplicates can occur in the hashset, and that making a node preserves
    // that property. To track that, the code 'simulates' a pointer address being assigned
    // in this ghost variable ptr_addresses. The values in the hashmap does not matter,
    // but they're assigned to hashmap length at the moment of assignment.
    ghost ptr_addresses: Map<Rc<Node>, nat>,
}

impl Bdd {
    spec fn well_formed(&self) -> bool {
        &&& forall|a: Rc<Node>, b: Rc<Node>|
            a == b && self.values@.contains(a) && self.values@.contains(b)
                <==> #[trigger] self.ptr_addresses[a] == #[trigger] self.ptr_addresses[b]
                && self.ptr_addresses.contains_key(a) && self.ptr_addresses.contains_key(b)
        &&& forall|a: Rc<Node>|
            self.values@.contains(a) <==> self.ptr_addresses.contains_key(
                a,
            )
        // All are in the hashmap already:
        &&& forall|node: Rc<Node>|
            self.values@.contains(node) ==> match *node {
                Node::Node { left, right, .. } => self.values@.contains(left)
                    && self.values@.contains(right),
                _ => true,
            }
    }

    fn get(&self, key: &Rc<Node>) -> (result: Option<&Rc<Node>>)
        requires
            self.well_formed(),
        ensures
            self.well_formed(),
            match result {
                Some(k) => self.values@.contains(*key) && k == key,
                None => !self.values@.contains(*key),
            },
    {
        let result = self.values.get(key);

        proof {
            // TODO: try to remove the admit here.
            // These 3 are not sufficient to prove it
            // broadcast use vstd::set::group_set_axioms;
            // broadcast use vstd::set_lib::group_set_lib_default;
            // broadcast use vstd::set_lib::group_set_properties;
            admit();
        }

        result
    }

    // As a workaround for:
    // The verifier does not yet support the following Rust feature: ==/!= for non smt equality types
    fn equal(&self, a: &Rc<Node>, b: &Rc<Node>) -> (result: bool)
        requires
            self.well_formed(),
            self.values@.contains(*a),
            self.values@.contains(*b),
        ensures
            self.well_formed(),
            result ==> (**a == **b),
            (**a == **b) ==> result,
    {
        use Node::{True, False};

        match (&**a, &**b) {
            (True, True) => true,
            (False, False) => true,
            (
                Node::Node { var: v1, left: l1, right: r1 },
                Node::Node { var: v2, left: l2, right: r2 },
            ) => v1 == v2 && self.rc_ptr_eq(l1, l2) && self.rc_ptr_eq(r1, r2),
            _ => false,
        }
    }

    fn insert(&mut self, key_and_value: Rc<Node>)
        requires
            !(old(self).values@.contains(key_and_value)),
            old(self).well_formed(),
        ensures
            self.values@.contains(key_and_value),
            self.well_formed(),
            // Nothing else is deleted, if something was previously in the set, it is still in the set
            forall|x: Rc<Node>| old(self).values@.contains(x) ==> self.values@.contains(x),
    {
        let ghost old_values = self.values@;
        let ghost old_ptr_addresses = self.ptr_addresses;

        // This line is crucial - why?
        // Because vstd::set::axiom_set_insert_same (as seen in the documentation) only
        // triggers on `s.insert(a).contains(a)` for a: A, Set<A>.
        // Only then we can prove that the newly inserted value is contained in the set.
        assert(self.values@.insert(key_and_value).contains(key_and_value));

        self.values.insert(key_and_value);
        // assert(self.values@.contains(key_and_value)); // FAILS

        proof {
            self.ptr_addresses = self.ptr_addresses.insert(key_and_value, self.ptr_addresses.len());

            // TODO: remove this admit
            admit();
        }
    }

    // Verifier does not support Rc::ptr_eq. So, we need a fix.
    // The following does not work. The function signature must match,
    // thus we must insert <T, A: std::alloc::Allocator>, but that is an
    // unstable API.
    // assume_specification<T>[std::rc::Rc::ptr_eq](a: &Rc<T>, b: &Rc<T>) -> bool;
    #[verifier::external_body]
    fn rc_ptr_eq(&self, a: &Rc<Node>, b: &Rc<Node>) -> (result: bool)
        requires
            self.well_formed(),
        ensures
            result ==> (self.ptr_addresses[*a] == self.ptr_addresses[*b]),
            (self.values@.contains(*a) && self.values@.contains(*b) && self.ptr_addresses[*a]
                == self.ptr_addresses[*b]) ==> result,
    {
        Rc::ptr_eq(a, b)
    }
}

#[derive(PartialEq, Eq, Hash)]
enum Node {
    False,
    True,
    Node { var: i32, left: Rc<Node>, right: Rc<Node> },
}

// ====================
// == Specifications ==
// ====================
spec fn node_false() -> Node {
    Node::False
}

spec fn node_true() -> Node {
    Node::True
}

spec fn node_and(l: Node, r: Node) -> Node
    decreases l, r,
{
    match (l, r) {
        (Node::True, _) => r,
        (_, Node::True) => l,
        (Node::False, _) | (_, Node::False) => Node::False,
        (
            Node::Node { var: vara, left: lefta, right: righta },
            Node::Node { var: varb, left: leftb, right: rightb },
        ) => {
            if vara < varb {
                node_if(vara as int, node_and(*lefta, r), node_and(*righta, r))
            } else if vara == varb {
                node_if(vara as int, node_and(*lefta, *leftb), node_and(*righta, *rightb))
            } else {
                node_if(varb as int, node_and(l, *leftb), node_and(l, *rightb))
            }
        },
    }
}

spec fn node_not(a: Node) -> Node
    decreases a,
{
    match a {
        Node::True => Node::False,
        Node::False => Node::True,
        Node::Node { var, left, right } => { node_if(var as int, node_not(*left), node_not(*right))
        },
    }
}

spec fn node_if(var: int, left: Node, right: Node) -> Node {
    if left =~= right {
        left
    } else {
        Node::Node { var: var as i32, left: Rc::new(left), right: Rc::new(right) }
    }
}

spec fn assignment_contains_all(node: Node, assignment: Map<i32, bool>) -> bool
    decreases node,
{
    match node {
        Node::False => true,
        Node::True => true,
        Node::Node { var, left, right } => assignment.contains_key(var) && assignment_contains_all(
            *left,
            assignment,
        ) && assignment_contains_all(*right, assignment),
    }
}

spec fn eval_node(node: Node, assignment: Map<i32, bool>) -> bool
    recommends
        assignment_contains_all(node, assignment),
    decreases node,
{
    match node {
        Node::True => true,
        Node::False => false,
        Node::Node { var, left, right } => {
            if assignment[var] {
                eval_node(*left, assignment)
            } else {
                eval_node(*right, assignment)
            }
        },
    }
}

// ===============================================
// ==== Correctness Proofs of Specifications =====
// ===============================================
// This is a simple property - automatically proven
proof fn node_if_correctness(var: int, left: Node, right: Node, assignment: Map<i32, bool>)
    requires
        assignment_contains_all(left, assignment),
        assignment_contains_all(right, assignment),
    ensures
        eval_node(node_if(var, left, right), assignment) == if assignment[var as i32] {
            eval_node(left, assignment)
        } else {
            eval_node(right, assignment)
        },
    decreases left, right,
{
}

// Proof that `node_and` exactly takes A and B.
proof fn and_correctness(a: Node, b: Node, assignment: Map<i32, bool>)
    requires
        assignment_contains_all(a, assignment),
        assignment_contains_all(b, assignment),
    ensures
        eval_node(node_and(a, b), assignment) == (eval_node(a, assignment) && eval_node(
            b,
            assignment,
        )),
    decreases a, b,
{
    // By induction:
    match (a, b) {
        (Node::True, Node::True) => {},
        (Node::True, Node::False) | (Node::False, Node::True) => {},
        (Node::False, Node::False) => {},
        (Node::True, Node::Node { var, left, right }) => {},
        (Node::False, Node::Node { var, left, right }) => {},
        (Node::Node { var, left, right }, Node::False) => {},
        (Node::Node { var, left, right }, Node::True) => {},
        (
            Node::Node { var: vara, left: lefta, right: righta },
            Node::Node { var: varb, left: leftb, right: rightb },
        ) => {
            if vara < varb {
                and_correctness(*lefta, b, assignment);
                and_correctness(*righta, b, assignment);
                // node_if_correctness(vara as int, node_and(*lefta, b), node_and(*righta, b), assignment);
            } else if vara == varb {
                and_correctness(*lefta, *leftb, assignment);
                and_correctness(*righta, *rightb, assignment);
                // Automatically proven, but otherwise:
                // node_if_correctness(vara as int, node_and(*lefta, *leftb), node_and(*righta, *rightb), assignment);
            } else {
                and_correctness(a, *leftb, assignment);
                and_correctness(a, *rightb, assignment);
                // node_if_correctness(varb as int, node_and(a, *leftb), node_and(a, *rightb), assignment);
            }
        },
    }
}

// Proof that `node_not` exactly negates the decision.
proof fn not_correctness(node: Node, assignment: Map<i32, bool>)
    requires
        assignment_contains_all(node, assignment),
    ensures
        eval_node(node_not(node), assignment) == !eval_node(node, assignment),
    decreases node,
{
    match node {
        Node::True | Node::False => {
            // Simple, not needed:
            // assert(eval_node(node_not(node), assignment) == !eval_node(node, assignment));
        },
        Node::Node { var, left, right } => {
            // Induction:
            not_correctness(*left, assignment);
            not_correctness(*right, assignment);
        },
    }
}

// ================================
// ==== Library Implementation ====
// ================================
fn mk_node(b: &mut Bdd, n: Node) -> (result: Rc<Node>)
    requires
        old(b).well_formed(),
    ensures
        b.well_formed(),
        b.values@.contains(result),
        *result =~= n,
        // Nothing is deleted
        forall|x: Rc<Node>| old(b).values@.contains(x) ==> b.values@.contains(x),
{
    let rc_node = Rc::new(n);
    match b.get(&rc_node) {
        Some(existing) => Rc::clone(existing),
        None => {
            assert(*Rc::clone(&rc_node) == &rc_node);
            assert(!b.values@.contains(rc_node));

            b.insert(Rc::clone(&rc_node));
            rc_node
        },
    }
}

fn mk_true(b: &mut Bdd) -> (result: Rc<Node>)
    requires
        old(b).well_formed(),
    ensures
        b.well_formed(),
        b.values@.contains(result),
        *result =~= node_true(),
        // Nothing else is deleted, if something was previously in the set, it is still in the set
        forall|x: Rc<Node>| old(b).values@.contains(x) ==> b.values@.contains(x),
{
    mk_node(b, Node::True)
}

fn mk_false(b: &mut Bdd) -> (result: Rc<Node>)
    requires
        old(b).well_formed(),
    ensures
        b.well_formed(),
        b.values@.contains(result),
        *result =~= node_false(),
        // Nothing else is deleted, if something was previously in the set, it is still in the set
        forall|x: Rc<Node>| old(b).values@.contains(x) ==> b.values@.contains(x),
{
    mk_node(b, Node::False)
}

fn mk_if(b: &mut Bdd, var: i32, left: Rc<Node>, right: Rc<Node>) -> (result: Rc<Node>)
    requires
        old(b).values@.contains(left),
        old(b).values@.contains(right),
        old(b).well_formed(),
    ensures
        b.well_formed(),
        b.values@.contains(result),
        *result =~= node_if(var as int, *left, *right),
        // Nothing else is deleted, if something was previously in the set, it is still in the set
        forall|x: Rc<Node>| old(b).values@.contains(x) ==> b.values@.contains(x),
{
    // The verifier does not yet support the following Rust feature: ==/!= for non smt equality types
    if b.equal(&left, &right) {
        left
    } else {
        mk_node(b, Node::Node { var, left, right })
    }
}

fn mk_var(b: &mut Bdd, v: i32) -> (result: Rc<Node>)
    requires
        old(b).well_formed(),
    ensures
        b.well_formed(),
        b.values@.contains(result),
        // Nothing else is deleted, if something was previously in the set, it is still in the set
        forall|x: Rc<Node>| old(b).values@.contains(x) ==> b.values@.contains(x),
{
    let tr = mk_true(b);
    let fls = mk_false(b);

    mk_if(b, v, tr, fls)
}

/// Challenge 2 - 3a. Since `node_and` is correct (see above), and this
/// function returns the same result as `node_and` (as proven below),
/// this function is also correct.
fn mk_and(b: &mut Bdd, l: &Rc<Node>, r: &Rc<Node>) -> (result: Rc<Node>)
    requires
        old(b).well_formed(),
        old(b).values@.contains(*l),
        old(b).values@.contains(*r),
    ensures
        b.well_formed(),
        b.values@.contains(result),
        *result =~= node_and(**l, **r),  // see proof `and_correctness`
        // Nothing else is deleted, if something was previously in the set, it is still in the set
        forall|x: Rc<Node>| old(b).values@.contains(x) ==> b.values@.contains(x),
    decreases l, r,
{
    match (&**l, &**r) {
        (Node::True, _) => Rc::clone(r),
        (_, Node::True) => Rc::clone(l),
        (Node::False, _) | (_, Node::False) => mk_false(b),
        (
            Node::Node { var: vara, left: lefta, right: righta },
            Node::Node { var: varb, left: leftb, right: rightb },
        ) => {
            if vara < varb {
                let left_and = mk_and(b, &lefta, r);
                let right_and = mk_and(b, &righta, r);
                mk_if(b, *vara, left_and, right_and)
            } else if vara == varb {
                let left_and = mk_and(b, &lefta, &leftb);
                let right_and = mk_and(b, &righta, &rightb);
                mk_if(b, *vara, left_and, right_and)
            } else {
                let left_and = mk_and(b, l, &leftb);
                let right_and = mk_and(b, l, &rightb);
                mk_if(b, *varb, left_and, right_and)
            }
        },
    }
}

/// Challenge 2 - 3b. Since `node_not` is correct (see above), and this
/// function returns the same result as `node_not` (as proven below),
/// this function is also correct.
fn mk_not(b: &mut Bdd, n: &Rc<Node>) -> (result: Rc<Node>)
    requires
        old(b).well_formed(),
    ensures
        b.well_formed(),
        b.values@.contains(result),
        *result == node_not(**n),  // see proof `not_correctness`
        // Nothing else is deleted, if something was previously in the set, it is still in the set
        forall|x: Rc<Node>| old(b).values@.contains(x) ==> b.values@.contains(x),
    decreases n,
{
    match &**n {
        Node::True => mk_false(b),
        Node::False => mk_true(b),
        Node::Node { var, left, right } => {
            let not_left = mk_not(b, left);
            let not_right = mk_not(b, right);
            let result = mk_if(b, *var, not_left, not_right);

            result
        },
    }
}

} // verus!
