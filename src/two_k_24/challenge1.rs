use vstd::prelude::*;

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

// Represents strings as a vector of bytes. If no string empty => empty vector.
struct Rope {
    left: Option<Box<Rope>>,
    right: Option<Box<Rope>>,
    value: Vec<u8>,
    weight: u32,
}

impl Rope {
    spec fn well_formed(self) -> bool
        decreases self,
    {
        &&& self.value.len() > 0 <==> self.left.is_none() && self.right.is_none()
        &&& self.left.is_some() ==> self.left.unwrap().well_formed()
        &&& self.right.is_some() ==> self.right.unwrap().well_formed()
    }

    spec fn represents(self) -> Seq<u8>
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

    // Challenge 1
    // Or, if you want a full appropriate data structure, you could implement display :)
    // We have proven that it is memory safe (thanks, Rust)
    // and that it terminates (variant on to_str_recurse)
    #[allow(unused)]
    fn to_str_basic(&self) -> (result: Vec<u8>)
        requires
            self.well_formed(),
        ensures
            self.represents() == result@,
            self.well_formed()
    {
        let mut v = Vec::new();
        self.to_str_recurse(&mut v);
        v
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
                    string@ == old_string + self.value@.subrange(0, i as int)
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
