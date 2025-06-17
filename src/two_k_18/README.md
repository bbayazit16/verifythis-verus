# 2018

## Challenge 2
- Uses the [VerCors solution](https://github.com/utwente-fmt/vercors/blob/dev/examples/verifythis/2018/challenge2.pvl), with additional invariants and assertions to help Verus.
- Initially, I attempted to verify the problem on my own. I discovered that the sequence followed a pattern very similar to fibonacci, and found a closed-form solution. In fact, the exact sequence is [OEIS A005252](https://oeis.org/A005252). Here's an O(1) algorithm:

```py
from math import sqrt

φ = (1 + sqrt(5)) / 2
DELTA = (1, 0, -1, -1, 0, 1)

def a(n: int) -> int:
    fib = round(φ**(n + 2) / sqrt(5))
    return (fib + DELTA[n % 6]) // 2
```

Perhaps someone should try verifying this solution as well? I couldn't find an easy way to prove the correctness this way.

- It's hard to verify that there won't be any overflows in Rust. I believe it might require reasoning about the sequence above, or some other way. Or, you could put an upper bound on the maximum value computed (which is what I did), and show the sequence is monotonic (which I didn't do). In my solution, the restriction is for values `4 <= i <= 81` (you could easily change the solution to accept i=0,1,2,3 as well with a simple if statement).
- [Project Euler Original problem](https://projecteuler.net/problem=114)
- Another trick is to heavily rely on `assert(...) by (compute);` to help compute bounds.
