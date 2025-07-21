/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Generalization.IMO2020N5.Defs
/- ... -/

/-!
# IMO 2020 N5 (Generalized)

Let $(M, ⬝)$ be a *cancellative* abelian monoid.
By cancellative, we mean that for any $a, b, c ∈ M$,
  $ac = bc$ implies $a = b$ and $ab = ac$ implies $b = c$.
(See `CancelCommMonoid` for the `mathlib` implementation.)
Given a function $f : ℕ⁺ → M$, we say that a positive integer $n$ is $f$-*nice* if
  $f(a) = f(b)$ holds for any $a, b ∈ ℕ⁺$ with $a + b = n$.
A monoid homomorphism $f : ℕ⁺ → M$ is called *good* if
  there are infinitely many $f$-nice integers.
Find all good monoid homomorphisms.

### Progress

Given a prime $p$, we say that $f$ is *$p$-locally good* if every power of $p$ is $f$-nice.
We just say that $f$ is *locally good* if it is $p$-locally good for some prime $p$.
We say that $f$ is *globally good* if there are infinitely many $f$-nice primes.
Then we have the following:
1. Every good homomorphisms are either locally good or globally good.
2. Every $p$-locally good homomorphisms $f$ are of the form
  $$ f(n) = c^{ν_p(n)} χ(n/p^{ν_p(n)}), $$ where $c ∈ M$ is a fixed element
  and $χ : 𝔽ₚˣ → M$ is a monoid homomorphism with $χ(-1) = 1$.
  In particular, if $M$ is torsion-free, they are all of the form $n ↦ c^{ν_p(n)}$.
3. The all-one map is the only globally good homomorphism if $M$ is torsion-free.
4. The all-one map is the only homomorphism that is $p$-locally good for two distinct $p$,
  and is also the only one that is globally good and $p$-locally good for some $p$.

In addition, the zero map is NOT the only globally good homomorphism over $M = C_p$.
Here $C_p$ is the cyclic group of order $p$.
The proof requires some advanced results in algebraic number theory.
The case $p = 2$ only requires Dirichlet's theorem and quadratic reciprocity.

### References

The author has put up a solution on AoPS.
See [here](https://artofproblemsolving.com/community/c6h2625925p29340833),
  post #40 by **BlazingMuddy**.
We implement this solution to classify good homomorphisms when $M$ is torsion-free.

### TODO

Implement everything.
(For now, implement everything except the case $p = 2$.)
-/

namespace IMOSLGeneralization
namespace IMO2020N5
