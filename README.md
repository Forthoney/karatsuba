# karatsuba
An provably correct implementation of the Karatsuba multiplication algorithm in Lean.

The [Karatsuba algorithm](https://en.wikipedia.org/wiki/Karatsuba_algorithm)
is a "fast" multiplication algorithm for arbitrary precision integer multiplication
where fast means "better than O(n^2)".
It is reasonably practical and
libraries such as GMP use it for multiplication of very large numbers.

Ironically, this implies Lean programmers probably should not use my implementation
when running code.
Lean's runtime also uses GMP for arithmetic on Nats,
meaning for sufficiently large Nats,
GMP's ultra-optimized karatsuba algorithm will kick in anyways.
