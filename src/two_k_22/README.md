# 2022

## Challenge 1
- Only tasks 1 and 2. There is also a rough idea for task 3, but it is not proven.
- Just like challenge 1 from 2016 (except this time 3D instead of 2D), Verus fails on mutable 3D arrays. As a solution, I had to specify `safe_set_3d` and `three_d_vec_with_capacity` as external bodies, which mutate a 3D vec and create a 3D vec with the given default value, respectively. The latter is needed because Verus does not support `vec![vec![vec![0; ...]; ...]; ...]`.
- It was difficult to work with spec closures in Verus. While I initially coded a `array_max_by` function to find the maximum value in a vec by a closure, I had to switch to using macros (that generate max by functions) instead. While my implementation works, I couldn't find a way to show propery that some function accepts my prerequisites `call_requires` (I understand this sounds trivial, but for some reason I couldn't get it working when passing in closures). I have left my original implementation in the code (although it is unused).

## Challenge 2
- Only tasks 1 and 2. Other tasks were harder to implement (as also acknowledged in the challenge report).
- A takeaway is the fact that generics are problematic. Initially, I added generics to struct: `Sr<T: PartialOrd>` to make the algorithm generally applicable. But, when comparing elements, we get the error that verifier does not support cmp or arithmetic for non smt arithmetic types. Thus, a simplification was using `Vec<u32>` instead of `Vec<T>`.
- I suspect that partial solutions could easily be implemented for the rest of the tasks, given the current state of the code.
