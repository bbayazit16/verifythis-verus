use vstd::prelude::*;

verus! {

// Represents strings as a vector of bytes. If no string => empty vector.
pub struct Rope {
    pub left: Option<Box<Rope>>,
    pub right: Option<Box<Rope>>,
    pub value: Vec<u8>,
    pub weight: usize,
}

// Verus does not support auto-clone derivation
impl Clone for Rope {
    fn clone(&self) -> (result: Self)
        ensures
            self.well_formed() <==> result.well_formed(),
            self.represents()
                =~= result.represents(),  // and, as a result; same string length

        decreases self,
    {
        let result = Rope {
            left: match &self.left {
                Some(left_rope) => Some(Box::new((**left_rope).clone())),
                None => None,
            },
            right: match &self.right {
                Some(right_rope) => Some(Box::new((**right_rope).clone())),
                None => None,
            },
            value: self.value.clone(),
            weight: self.weight,
        };

        result
    }
}

// You could add generics here
fn vec_subrange(v: &Vec<u8>, start: usize, end: usize) -> (result: Vec<u8>)
    requires
        start <= end,
        end <= v.len(),
    ensures
        result@ == v@.subrange(start as int, end as int),
        result.len() == end - start,
{
    let mut result = Vec::new();
    for i in start..end
        invariant
            start <= i <= end <= v.len(),
            result@ =~= v@.subrange(start as int, i as int),
    {
        result.push(v[i]);
    }
    result
}

impl Rope {
    pub open spec fn well_formed(self) -> bool
        decreases self,
    {
        &&& self.value@.len() > 0 ==> self.left.is_none() && self.right.is_none()
        &&& self.weight == 0 ==> self.left.is_none()
        &&& self.left.is_some() ==> self.left.unwrap().well_formed()
        &&& self.right.is_some() ==> self.right.unwrap().well_formed()
        &&& self.weight == match self.left {
            Some(left_rope) => left_rope.str_len_spec(),
            None => self.value@.len(),
        }
    }

    pub open spec fn represents(self) -> Seq<u8>
        decreases self,
    {
        if self.value@.len() > 0 {
            self.value@
        } else {
            match (self.left, self.right) {
                (None, None) => Seq::empty(),
                (None, Some(s)) => s.represents(),
                (Some(s), None) => s.represents(),
                (Some(left), Some(right)) => left.represents() + right.represents(),
            }
        }
    }

    pub open spec fn str_len_spec(self) -> nat {
        self.represents().len()
    }

    // Challenge 0, tasks (a) and (b)
    // Or, if you want a full appropriate data structure, you could implement display :)
    // We have proven that it is memory safe (thanks, Rust!) (although the compiler is not verified
    // let's assume that Rust programs are memory safe ;) )
    // and that it terminates (variant on to_str_recurse)
    #[allow(unused)]
    fn to_str(&self) -> (result: Vec<u8>)
        requires
            self.well_formed(),
        ensures
            self.represents() == result@,
            self.well_formed(),
    {
        let mut v = Vec::new();
        self.to_str_recurse(&mut v);
        v
    }

    // Challenge 0, task (c)
    #[allow(unused)]
    fn str_len(&self) -> (result: usize)
        requires
            self.well_formed(),
            self.str_len_spec() < usize::MAX,
        ensures
            self.str_len_spec() == result,
            self.well_formed(),
        decreases self,
    {
        if self.left.is_none() && self.right.is_none() {
            self.weight
        } else {
            self.weight + match &self.right {
                Some(right_rope) => right_rope.str_len(),
                None => 0,
            }
        }
    }

    // Challenge 0, task (d)
    // The signature on the challenge asks to produce a new rope.
    // For that reason, we need to own the left/right variables,
    // or clone the references.
    #[allow(unused)]
    fn concat(left: Rope, right: Rope) -> (result: Rope)
        requires
            left.well_formed(),
            right.well_formed(),
            left.str_len_spec() < i32::MAX,
            right.str_len_spec() < i32::MAX,
        ensures
            left.well_formed(),
            right.well_formed(),
            result.well_formed(),
            result.represents() == left.represents() + right.represents(),
    {
        let left_weight = left.str_len();
        Rope {
            left: if left_weight == 0 {
                None
            } else {
                Some(Box::new(left))
            },
            right: Some(Box::new(right)),
            value: Vec::new(),
            weight: left_weight,
        }
    }

    // Challenge 0, task (e)
    // Again, just like concat, we need to produce a new Rope.
    // `len` characters removed from rope starting at `i`.
    #[allow(unused)]
    fn delete(rope: &Rope, i: usize, len: usize) -> (result: Rope)
        requires
            rope.well_formed(),
            i + len <= rope.str_len_spec() < i32::MAX,
        ensures
            result.well_formed(),
            result.represents() =~= rope.represents().subrange(0, i as int)
                + rope.represents().subrange((i + len) as int, rope.str_len_spec() as int),
            result.str_len_spec() == rope.str_len_spec() - len,
    {
        let mut rope_clone = rope.clone();

        let (left, remaining) = Rope::split(rope_clone, i);
        let (_, right) = Rope::split(remaining, len);
        Rope::concat(left, right)
    }

    fn split(rope: Rope, i: usize) -> (results: (Rope, Rope))
        requires
            rope.well_formed(),
            0 <= i <= rope.str_len_spec() < i32::MAX,
        ensures
            results.0.well_formed(),
            results.1.well_formed(),
            results.0.represents() + results.1.represents() =~= rope.represents(),
            results.0.str_len_spec() == i,
            results.1.str_len_spec() == rope.str_len_spec() - i,
            results.0.represents() =~= rope.represents().subrange(0, i as int),
            results.1.represents() =~= rope.represents().subrange(
                i as int,
                rope.str_len_spec() as int,
            ),
        decreases rope,
    {
        if rope.left.is_none() && rope.right.is_none() {
            let left_value = vec_subrange(&rope.value, 0, i);
            let right_value = vec_subrange(&rope.value, i, rope.value.len());
            let left = Rope::make_leaf(left_value);
            let right = Rope::make_leaf(right_value);

            assert(rope.represents() =~= left.represents() + right.represents());

            (
                left,
                right,
            )
            // let right = Rope::make_leaf(vec_subrange(&rope.value, i, rope.value.len()));
            // rope.value = vec_subrange(&rope.value, 0, i);
            // rope.weight = i;
            // (rope, right)

        } else if i < rope.weight {
            let (left, right) = Rope::split(*rope.left.unwrap(), i);
            let (r1, r2) = match rope.right {
                Some(right_rope) => (left, Rope::concat(right, *right_rope)),
                None => { (left, right) },
            };
            assert(r1.represents() + r2.represents() =~= rope.represents());
            (r1, r2)
        } else if i > rope.weight {
            let (left, right) = Rope::split(*rope.right.unwrap(), i - rope.weight);
            let (r1, r2) = match rope.left {
                Some(left_rope) => (Rope::concat(*left_rope, left), right),
                None => (left, right),
            };
            assert(r1.represents() + r2.represents() =~= rope.represents());
            (r1, r2)
        } else {
            if i == 0 {
                (Rope::make_leaf(Vec::new()), rope)
            } else {
                let left_rope = rope.left.unwrap();
                match rope.right {
                    Some(right_rope) => (*left_rope, *right_rope),
                    None => (*left_rope, Rope::make_leaf(Vec::new())),
                }
            }
        }
    }

    fn make_leaf(value: Vec<u8>) -> (result: Rope)
        requires
            value@.len() < i32::MAX,
        ensures
            result.well_formed(),
            result.represents() =~= value@,
    {
        let weight = value.len();
        Rope { left: None, right: None, value, weight }
    }

    fn to_str_recurse(&self, string: &mut Vec<u8>)
        requires
            self.well_formed(),
        ensures
            string@ =~= old(string)@ + self.represents(),
            self.well_formed(),
        decreases self,
    {
        if self.value.len() != 0 {
            // extend is not supported
            let ghost old_string = string@;
            for i in 0..self.value.len()
                invariant
                    self.well_formed(),
                    string@ == old_string + self.value@.subrange(0, i as int),
            {
                string.push(self.value[i]);
                assert(string@ == old_string + self.value@.subrange(0, (i + 1) as int));
            }
            assert(self.value@.subrange(0, self.value.len() as int) == self.value@);
        } else {
            if let Some(left) = &self.left {
                left.to_str_recurse(string);
            }
            if let Some(right) = &self.right {
                right.to_str_recurse(string);
            }
        }
    }
}

} // verus!
