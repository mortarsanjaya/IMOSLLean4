/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

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

This file sets up the problem and proves some basic properties.
-/

namespace IMOSLGeneralization
namespace IMO2020N5
