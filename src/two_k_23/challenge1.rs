use vstd::prelude::*;

verus! {

struct Cell {
    #[allow(unused)]
    value: i32,
    next: Option<Box<Cell>>,
}

spec fn cell_len(cell: Option<Cell>) -> nat
    decreases cell,
{
    match cell {
        Some(c) => 1 + cell_len(unbox_ptr(c.next)),
        None => 0,
    }
}

spec fn unbox_ptr(cell: Option<Box<Cell>>) -> Option<Cell> {
    match cell {
        Some(c) => Some(*c),
        None => None,
    }
}

spec fn box_ptr(c: Option<Cell>) -> Option<Box<Cell>> {
    match c {
        Some(mut inner) => { Some(Box::new(inner)) },
        None => None,
    }
}

/// Use with reversed(None, <list>), the first argument is the accumulator.
/// You could also abstract this as helper function, but it's quite enough for the proof.
spec fn reversed(cell: Option<Cell>, remaining: Option<Cell>) -> Option<Cell>
    decreases remaining,
{
    match remaining {
        None => cell,
        Some(rest) => {
            let head_val = rest.value;
            let next_ptr = rest.next;

            let new_rest = Some(Cell { value: head_val, next: box_ptr(cell) });
            reversed(new_rest, unbox_ptr(next_ptr))
        },
    }
}

fn list_reversal_helper(
    mut head: Option<Box<Cell>>,
    Ghost(original_head): Ghost<Option<Box<Cell>>>,
) -> (new_ptr: Option<Box<Cell>>)
    requires
        original_head == head,
    ensures
        // This block would be parsed as the function/loop body, but it is followed immediately by another block
        // (if you meant this block to be part of the specification, try parenthesizing it)
        // Added block - in case let statements are required;
        ({ reversed(None, unbox_ptr(original_head)) =~= unbox_ptr(new_ptr) }),
{
    let mut prev: Option<Box<Cell>> = None;

    while head.is_some()
        invariant
            reversed(unbox_ptr(prev), unbox_ptr(head)) =~= reversed(
                None,
                unbox_ptr(original_head),
            ),
        
    // Technically, we could just do `decreases head`.
    // However, there's a bug (either this, or something similar) with Verus that
    // prevents us from doing so:
    // https://github.com/verus-lang/verus/issues/1222
    // Verus panic when checking termination on a Seq of recursive enums
        decreases cell_len(unbox_ptr(head)),
    {
        let mut current = head.unwrap();
        head = current.next.take();
        current.next = prev;
        prev = Some(current);
    }

    // These assertions are not needed - but good to use when debugging
    // assert(reversed(unbox_ptr(prev),
    //                  unbox_ptr(head))
    //           =~= reversed(None, unbox_ptr(original_head)));
    // assert(head.is_none());
    // assert(reversed(unbox_ptr(prev), None) =~= unbox_ptr(prev));
    // assert(unbox_ptr(prev) =~= reversed(None, unbox_ptr(original_head)));

    prev
}

// Challenge 1
#[allow(unused)]
fn list_reversal(head: Option<Box<Cell>>) -> (new_ptr: Option<Box<Cell>>)
    ensures
        reversed(None, unbox_ptr(head)) =~= unbox_ptr(new_ptr),
{
    list_reversal_helper(head, Ghost(head))
}

} // verus!
