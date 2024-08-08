/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs

/-!
# IMO 2017 A6 (P2, Definitions)

Let $R$ be a ring.
Determine all functions $f : R → R$ such that, for any $x, y ∈ R$,
$$ f(f(x) f(y)) + f(x + y) = f(xy). $$

This file defines the functional equation and prove the most basic properties.
We say that $f$ is
* `good` if it satisfies the above functional equation;
* `ReducedGood` if in addition, $f$ has no non-zero period.

The `good` functions are characterized for a decent amount of subcases on $R$.
The file `IMOSLLean4/IMO2017/A6/A6.lean` collects all the main results.
-/

namespace IMOSL
namespace IMO2017A6

variable [NonUnitalNonAssocSemiring R]

/-- The problem. -/
def good (f : R → R) := ∀ x y : R, f (f x * f y) + f (x + y) = f (x * y)

lemma good.map_map_zero_mul_map {f : R → R} (hf : good f) (x) :
    f (f 0 * f x) + f x = f 0 := by
  specialize hf 0 x; rwa [zero_add, zero_mul] at hf

structure ReducedGood (f : R → R) : Prop where
  is_good : good f
  period_imp_eq (c d) (_ : ∀ x, f (x + c) = f (x + d)) : c = d

lemma ReducedGood.period_imp_zero (hf : ReducedGood f) (h0 : ∀ x : R, f (x + c) = f x) :
    c = 0 :=
  hf.period_imp_eq _ _ λ x ↦ by rw [h0, add_zero]
