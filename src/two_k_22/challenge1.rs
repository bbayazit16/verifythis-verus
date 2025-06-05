use vstd::prelude::*;

verus! {

// The verifier does not yet support the following Rust feature: div/mod on signed finite-width integers
// And, since the least possible point is (0, 0, 0), we represent Point by nat.
#[derive(Eq, PartialEq, Clone, Copy)]
struct Point {
    x: u32,
    y: u32,
    z: u32,
}

impl Point {
    // We could, more idiomatically, implement this with Add trait, but here's the problem:
    // The verifier does not yet support the following Rust feature: cmp or arithmetic for non smt arithmetic types
    fn add(self, rhs: Self) -> (result: Self)
        requires
            self.x + rhs.x <= u32::MAX,
            self.y + rhs.y <= u32::MAX,
            self.z + rhs.z <= u32::MAX,
        ensures
            result.x == self.x + rhs.x,
            result.y == self.y + rhs.y,
            result.z == self.z + rhs.z,
    {
        Point { x: self.x + rhs.x, y: self.y + rhs.y, z: self.z + rhs.z }
    }

    fn div_by(self, rhs: u32) -> (result: Self)
        requires
            rhs != 0,
    {
        Point { x: self.x / rhs, y: self.y / rhs, z: self.z / rhs }
    }

    // We cannot derive default, because:
    // cannot use function `main::two_k_22::challenge1::Point::default` which is ignored because it is
    // either declared outside the verus! macro or it is marked as `external`
    fn default() -> (result: Self)
        ensures
            result.x == 0,
            result.y == 0,
            result.z == 0,
    {
        Point { x: 0, y: 0, z: 0 }
    }
}

// .iter().map is not supported in Verus.
// My initial idea: to have array_max_by, and pass closures to capture x, y, z.
// However, while the function below is fully correct and passes verifciation, I could
// not get Verus to verify that closures verify prerequisite that:
//
// forall|i: int| #![trigger p[i]] 0 <= i < p@.len() ==> {
//  &&& call_requires(by, (p[i],)) &&& forall|ret: i32| call_ensures(by, (p[i],), ret) <==> ret == by_spec(p[i])
// }
//
// So I have switched to a macro instead.
//
//
// #[verifier::loop_isolation(false)]
// fn array_max_by(
//     p: &[Point],
//     by: impl Fn(Point) -> i32,
//     Ghost(by_spec): Ghost<spec_fn(Point) -> i32>,
// ) -> (result: Point)
//     requires
//         p.len() > 0,
//         forall|i: int|
//             #![trigger p[i]]
//             0 <= i < p@.len() ==> {
//                 &&& call_requires(by, (p[i],))
//                 &&& forall|ret: i32| call_ensures(by, (p[i],), ret) <==> ret == by_spec(p[i])
//             },
//     ensures
//         p@.contains(result),
//         forall|i: int| 0 <= i < p@.len() ==> by_spec(p[i]) <= by_spec(result),
// {
//     let mut max = p[0];
//     let ghost mut max_idx = 0int;
//     for i in 0..p.len()
//         invariant
//             forall|j: int| 0 <= j < i ==> by_spec(p@[j]) <= by_spec(max),
//             0 <= max_idx < p.len() && p[max_idx] == max,
//     {
//         if by(p[i]) >= by(max) {
//             max = p[i];
//             proof {
//                 max_idx = i as int;
//             }
//         }
//     }
//     max
// }


// Note: In the macro, the implies syntax (==>) was causing a syntax error. I have changed p ==> q to !p || q.
// Similarly, not including verus! again causes a syntax error as well.
macro_rules! max_by_what {
    ($name:ident, $field:ident) => {
        verus! {
            // The verifier does not yet support the following Rust feature: overloaded deref
            // (`std::vec::Vec<two_k_22::challenge1::Point>` is implicity converted to `[two_k_22::challenge1::Point]`
            // So we can't use &[Point].
            fn $name(p: &Vec<Point>) -> (result: Point)
            requires
                p.len() > 0
            ensures
                p@.contains(result),
                forall|i: int| #![trigger p[i]] !(0 <= i < p@.len()) || p[i].$field <= result.$field
        {
            let mut max = p[0];
            let ghost mut max_idx = 0int;

            for i in 0..p.len()
                invariant
                    forall|j: int| #![trigger p[j]] !(0 <= j < i) || p@[j].$field <= max.$field,
                    0 <= max_idx < p.len() && p[max_idx] == max
            {
                if p[i].$field >= max.$field {
                    max = p[i];
                    proof { max_idx = i as int; }
                }
            }
            max
        }}
    };
}

macro_rules! min_by_what {
    ($name:ident, $field:ident) => {
        verus! {
            // The verifier does not yet support the following Rust feature: overloaded deref
            // (`std::vec::Vec<two_k_22::challenge1::Point>` is implicity converted to `[two_k_22::challenge1::Point]`
            // So we can't use &[Point].
            fn $name(p: &Vec<Point>) -> (result: Point)
            requires
                p.len() > 0
            ensures
                p@.contains(result),
                forall|i: int| #![trigger p[i]] !(0 <= i < p@.len()) || p[i].$field >= result.$field
        {
            let mut max = p[0];
            let ghost mut max_idx = 0int;

            for i in 0..p.len()
                invariant
                    forall|j: int| #![trigger p[j]] !(0 <= j < i) || p@[j].$field >= max.$field,
                    0 <= max_idx < p.len() && p[max_idx] == max
            {
                if p[i].$field <= max.$field {
                    max = p[i];
                    proof { max_idx = i as int; }
                }
            }
            max
        }}
    };
}

max_by_what!(array_max_by_x, x);

max_by_what!(array_max_by_y, y);

max_by_what!(array_max_by_z, z);

min_by_what!(array_min_by_x, x);

min_by_what!(array_min_by_y, y);

min_by_what!(array_min_by_z, z);

fn abs(x: i32) -> (result: u32)
    requires
        x != i32::MIN,  // because -i32::MIN overflows

    ensures
        result == vstd::math::abs(x as int),
{
    if x >= 0 {
        x as u32
    } else {
        (-x) as u32
    }
}

// an `assume_specification` declaration must be at least as visible as the function it provides a spec for
// pub assume_specification[ u32::div_ceil ](a: u32, b: u32) -> (result: u32)
//     requires
//         b > 0,
//     ensures
//         exists|remainder: nat|
//             result == vstd::math::add(vstd::math::div(a as int, b as int), remainder as int),
//         result >= a / b,
//         result <= a / b + 1,
//         (a % b == 0) ==> result == a / b,
//         (a % b != 0) ==> result == a / b + 1,
//         result == div_ceil(a, b)
// ;

// We used `div_ceil` in the above `pub asssume_specification` (which is now commented).
// If we don't mark the function below as `pub open spec fn`, we get the error:
// in 'ensures' clause of public function, cannot refer to private function)
pub open spec fn div_ceil(a: u32, b: u32) -> u32
    recommends
        b > 0,
{
    if a % b == 0 {
        a / b
    } else {
        (a / b + 1) as u32
    }
}

// `alloc::vec::from_elem` is not supported (note: you may be able to add a Verus specification to this function with `assume_specification`)
// (note: the vstd library provides some specification for the Rust std library, but it is currently limited)
// Vec::with_capacity and then pushing back is a good way to circumvent this without #[verifier::external_body],
// but that causes the algorithm to realtively deviate from the original challenge.
// You could also use assume_specification here; though that would be harder to specify.
#[verifier::external_body]
fn three_d_vec_with_capacity<T>(
    outer: usize,
    middle: usize,
    inner: usize,
    default_value: T,
) -> (result: Vec<Vec<Vec<T>>>) where T: Copy
    ensures
        result@.len() == outer,
        forall|i: int| #![trigger result@[i]] 0 <= i < outer ==> result@[i]@.len() == middle,
        forall|i: int, j: int|
            #![trigger result@[i]@[j]]
            0 <= i < outer && 0 <= j < middle ==> result@[i]@[j]@.len() == inner,
        forall|i: int, j: int, k: int|
            #![trigger result@[i]@[j]@[k]]
            0 <= i < outer && 0 <= j < middle && 0 <= k < inner ==> result@[i]@[j]@[k]
                == default_value,
{
    vec![vec![vec![default_value; inner]; middle]; outer]
}

// The verifier does not yet support the following Rust feature: index for &mut not supported
// There are alternative ways to achieve this, such as pushing and simulating a 3D assignment;
// but that deviates from the original challenge code.
#[verifier::external_body]
fn safe_set_3d<T>(v: &mut Vec<Vec<Vec<T>>>, i: usize, j: usize, k: usize, value: T)
    requires
        // i is a valid index
        i < old(v)@.len(),
        // j is a valid index
        j < old(v)@[i as int]@.len(),
        // k is a valid index
        k < old(v)@[i as int]@[j as int]@.len(),
    ensures
        // overall vec length does not change
        v@.len() == old(v)@.len(),
        // nested vec lengths do not change
        forall|ri: int| #![trigger v@[ri]] 0 <= ri < v@.len() ==> v@[ri].len() == old(v)@[ri].len(),
        // nested, nested vec lenghts do not change
        forall|ri: int, rj: int|
            #![trigger v@[ri][rj]]
            0 <= ri < v@.len() && 0 <= rj < v@[ri].len() ==> v@[ri][rj].len() == old(
                v,
            )@[ri][rj].len(),
        // sets the value correctly
        v@[i as int][j as int][k as int] == value,
        // value is contained in the array after setting
        v@[i as int]@[j as int]@.contains(value),
        // all other indices remain the same
        forall|ri: int, rj: int, rk: int|
            #![trigger v@[ri][rj][rk]]
        // (for all valid indices) && (<apart from the current index>) ==> (index does not change)
            0 <= ri < v@.len() && 0 <= rj < v@[ri].len() && 0 <= rk < v@[ri][rj].len() && !(ri == i
                && rj == j && rk == k) ==> v@[ri][rj][rk] == old(v)@[ri][rj][rk],
{
    v[i][j][k] = value;
}

spec fn valid_3d_array_structure<T>(
    array: Seq<Vec<Vec<T>>>,
    outer: int,
    middle: int,
    inner: int,
) -> bool {
    &&& array.len() == outer
    &&& forall|i: int| #![trigger array[i]] 0 <= i < outer ==> array[i].len() == middle
    &&& forall|i: int, j: int|
        #![trigger array[i][j]]
        0 <= i < outer && 0 <= j < middle ==> array[i][j].len() == inner
}

proof fn lemma_floor_bounds(coord_diff: u32, coord_range: nat, voxel_size: u32)
    requires
        coord_diff <= coord_range,
        voxel_size > 0,
    ensures
        coord_diff / voxel_size <= coord_range / voxel_size as nat,
{
    // by (nonlinear_arith) can't capture outer conditions
    assert(coord_diff / voxel_size <= coord_range / voxel_size as nat) by (nonlinear_arith)
        requires
            coord_diff <= coord_range,
            voxel_size > 0,
    ;
}

spec fn count_nonzeros_3d(v: Seq<Vec<Vec<u32>>>) -> nat
    decreases v,
{
    if v.len() == 0 {
        0
    } else {
        count_nonzeros_2d(v.first()@) + count_nonzeros_3d(v.drop_first())
    }
}

spec fn count_nonzeros_2d(v: Seq<Vec<u32>>) -> nat
    decreases v,
{
    if v.len() == 0 {
        0
    } else {
        count_nonzeros_1d(v.first()@) + count_nonzeros_2d(v.drop_first())
    }
}

spec fn count_nonzeros_1d(v: Seq<u32>) -> nat
    decreases v,
{
    if v.len() == 0 {
        0
    } else {
        let first_is_zero = if v.first() != 0 {
            1nat
        } else {
            0
        };

        first_is_zero + count_nonzeros_1d(v.drop_first())
    }
}

// Useful for task 3
// proof fn lemma_count_all_zeros_is_zero_3d(v: Seq<Vec<Vec<u32>>>)
//     requires
//         forall|i: int, j: int, k: int|
//             #![trigger v[i][j][k]]
//             0 <= i < v.len() && 0 <= j < v[i].len() && 0 <= k < v[i][j].len() ==> v[i][j][k] == 0,
//     ensures
//         count_nonzeros_3d(v) == 0,
//     decreases v.len(),
// {
//     if v.len() == 0 {
//     } else {
//         lemma_count_all_zeros_is_zero_2d(v.first()@);
//         lemma_count_all_zeros_is_zero_3d(v.drop_first());
//     }
// }

// proof fn lemma_count_all_zeros_is_zero_2d(v: Seq<Vec<u32>>)
//     requires
//         forall|j: int, k: int|
//             #![trigger v[j][k]]
//             0 <= j < v.len() && 0 <= k < v[j].len() ==> v[j][k] == 0,
//     ensures
//         count_nonzeros_2d(v) == 0,
//     decreases v.len(),
// {
//     if v.len() == 0 {
//     } else {
//         lemma_count_all_zeros_is_zero_1d(v.first()@);
//         lemma_count_all_zeros_is_zero_2d(v.drop_first());
//     }
// }

// proof fn lemma_count_all_zeros_is_zero_1d(v: Seq<u32>)
//     requires
//         forall|k: int| #![trigger v[k]] 0 <= k < v.len() ==> v[k] == 0,
//     ensures
//         count_nonzeros_1d(v) == 0,
//     decreases v.len(),
// {
//     if v.len() == 0 {
//     } else {
//         lemma_count_all_zeros_is_zero_1d(v.drop_first());
//     }
// }

spec fn no_input_overflows(p: Seq<Point>) -> bool {
    // Note: writing more statements inside #![trigger a, b, c], etc. only restricts the trigger,
    // doesn't relax it. To make the trigger more relaxed, use #![trigger a] #![trigger b] #![trigger c] etc.
    // Also, each triggers must capture every free variable declared in forall.
    &&& forall|i: int|
        0 <= i < p.len() ==> {
            &&& #[trigger] p[i].x <= u16::MAX
            &&& #[trigger] p[i].y <= u16::MAX
            &&& #[trigger] p[i].z <= u16::MAX
        }
    &&& p.len() <= (u32::MAX as int / u16::MAX as int) as usize
}

// Challenge 1
#[verifier::loop_isolation(false)]
#[allow(unused)]
fn downsample(p: Vec<Point>, voxel_size: u32) -> (result: Vec<Point>)
    requires
        no_input_overflows(p@),
        voxel_size > 0,
        0 < p.len(),
        p.len() * u16::MAX as int <= i32::MAX,
        p.len() * u16::MAX as int <= i32::MAX,
    // Task 3:
    // ensures
    //     result@.len() <= p@.len()
{
    let (x_max_pt, y_max_pt, z_max_pt) = (
        array_max_by_x(&p),
        array_max_by_y(&p),
        array_max_by_z(&p),
    );
    let (x_min_pt, y_min_pt, z_min_pt) = (
        array_min_by_x(&p),
        array_min_by_y(&p),
        array_min_by_z(&p),
    );

    let (x_max, y_max, z_max) = (x_max_pt.x, y_max_pt.y, z_max_pt.z);
    let (x_min, y_min, z_min) = (x_min_pt.x, y_min_pt.y, z_min_pt.z);

    // Original approach in the algorithm breaks and causes index out of bounds?
    // - When x_max == x_min
    //  - num_vox_x is 0, no array
    // - When p[i].x == x_max AND (x_max - x_min) is non-zero exact multiple of voxel_size:
    //  - Say x_max == 8, p[i].x == 8, voxel_size == 4, x_min == 4.
    //  - Then num_vox_x = (x_max - x_min)/voxel_size = (8 - 4)/4 = 1
    //  - Then (p[i].x - x_min) / voxel_size = (8 - 4)/4 = 1
    //  - But we try to access index 1
    //
    // Thus, I have added +1 to each index, regardless.
    let (num_vox_x, num_vox_y, num_vox_z) = (
        abs(x_max as i32 - x_min as i32) / (voxel_size) + 1,
        abs(y_max as i32 - y_min as i32) / (voxel_size) + 1,
        abs(z_max as i32 - z_min as i32) / (voxel_size) + 1,
    );

    let mut voxel_array = three_d_vec_with_capacity(
        num_vox_x as usize,
        num_vox_y as usize,
        num_vox_z as usize,
        Point::default(),
    );

    let mut count_array = three_d_vec_with_capacity(
        num_vox_x as usize,
        num_vox_y as usize,
        num_vox_z as usize,
        0u32,
    );

    // assert(count_nonzeros_3d(count_array@) == 0) by {
    //     lemma_count_all_zeros_is_zero_3d(count_array@);
    // };

    // I tried to prove postconditions without keeping track by variables, but nothing works.
    // The key idea is to keep track of the total non-zero numbers.
    // We increment this whenever current count is incremented, and was previously 0.
    // Later, this becomes the length of the resulting vector.
    let ghost mut total_nonzeros: nat = 0;
    for i in 0..p.len()
        invariant
            valid_3d_array_structure(
                voxel_array@,
                num_vox_x as int,
                num_vox_y as int,
                num_vox_z as int,
            ),
            valid_3d_array_structure(
                count_array@,
                num_vox_x as int,
                num_vox_y as int,
                num_vox_z as int,
            ),
            total_nonzeros <= i,
            forall|vi: int, vj: int, vk: int|
                #![trigger voxel_array@[vi][vj][vk]]
                0 <= vi < num_vox_x && 0 <= vj < num_vox_y && 0 <= vk < num_vox_z ==> {
                    &&& voxel_array@[vi][vj][vk].x <= i * u16::MAX
                    &&& voxel_array@[vi][vj][vk].y <= i * u16::MAX
                    &&& voxel_array@[vi][vj][vk].z <= i * u16::MAX
                    &&& count_array@[vi][vj][vk] <= i
                },
    {
        let x_diff = (p[i].x - x_min) as u32;
        let y_diff = (p[i].y - y_min) as u32;
        let z_diff = (p[i].z - z_min) as u32;

        let (x_floored, y_floored, z_floored) = (
            x_diff / voxel_size,
            y_diff / voxel_size,
            z_diff / voxel_size,
        );

        proof {
            // We already know that 0 <= x_floored.
            // Here, we want to prove that x_floored < num_vox_x,
            // so that we can have 0 <= x_floored < num_vox_x,
            // which proves array accesses are not index out of bounds.
            // Same goes for other variables (x, y, z)
            let x_range = vstd::math::abs(x_max - x_min);
            lemma_floor_bounds(x_diff, x_range, voxel_size);

            let y_range = vstd::math::abs(y_max - y_min);
            lemma_floor_bounds(y_diff, y_range, voxel_size);

            let z_range = vstd::math::abs(z_max - z_min);
            lemma_floor_bounds(z_diff, z_range, voxel_size);
        }

        let current_pt = voxel_array[x_floored as usize][y_floored as usize][z_floored as usize];
        let current_count = count_array[x_floored as usize][y_floored as usize][z_floored as usize];

        // The verifier does not yet support the following Rust feature: index for &mut not supported
        // That's why safe_set_3d exists.
        safe_set_3d(
            &mut voxel_array,
            x_floored as usize,
            y_floored as usize,
            z_floored as usize,
            current_pt.add(p[i]),
        );

        proof {
            total_nonzeros =
            total_nonzeros + if current_count == 0 {
                1nat
            } else {
                0nat
            };
        }

        safe_set_3d(
            &mut count_array,
            x_floored as usize,
            y_floored as usize,
            z_floored as usize,
            current_count + 1,
        );
    }

    assert(total_nonzeros <= p.len());
    
    let mut pd = Vec::new();
    let ghost mut line_executions = 0nat;
    for i in 0..num_vox_x as usize
        invariant
            pd.len() == line_executions,
    {
        for j in 0..num_vox_y as usize
            invariant
                pd.len() == line_executions,
        {
            for k in 0..num_vox_z as usize
                invariant
                    pd.len() == line_executions,
            {
                if count_array[i][j][k] != 0 {
                    proof { line_executions = line_executions + 1 };
                    pd.push(voxel_array[i][j][k].div_by(count_array[i][j][k]));
                }
            }
        }
    }
    
    assert(pd.len() == line_executions);

    // Assertion fails!! - Fixing this would prove task 3.
    // assert(line_executions == total_nonzeros);
    
    pd
}

} // verus!
