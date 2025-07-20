/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs

/-!
# IMO 2012 A5 (Definitions)

Let $R$ be a ring and $S$ be a domain.
Find all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(xy + 1) = f(x) f(y) + f(x + y). $$

This file defines the functional equation and prove some basic properties.
We also define some notions; we say that $f$ is
* `good` if it satisfies the above functional equation;
* `NontrivialGood` if $f$ is good and $f(0) = -1$;
* `ReducedGood` if $f$ is non-trivial good and there is no non-zero $f$-periodic element.

The `NontrivialGood` functions are defined in the folder `A5Answers`.
They file `IMOSLLean4/IMO2012/A5/A5Answers/Common.lean` collects all these functions.
The file `IMOSLLean4/IMO2012/A5/A5.lean` proves that these are
  precisely the good functions, up to ring homomorphism.
-/

namespace IMOSL
namespace IMO2012A5

variable [NonAssocSemiring R] [Add S] [Mul S]

/-- The main problem. -/
def good (f : R → S) := ∀ x y : R, f (x * y + 1) = f x * f y + f (x + y)

theorem map_commute_of_commute [IsCancelAdd S]
    {f : R → S} (h : good f) (h0 : x * y = y * x) : f x * f y = f y * f x :=
  add_right_cancel (b := f (x + y)) (by rw [← h, h0, h, add_comm x])


variable [One S] [Zero S]

structure NontrivialGood (f : R → S) : Prop where
  is_good : good f
  map_zero_add_one : f 0 + 1 = 0

lemma NontrivialGood.map_zero {S} [AddGroupWithOne S] [Mul S]
    {f : R → S} (hf : NontrivialGood f) : f 0 = -1 :=
  eq_neg_of_add_eq_zero_left hf.map_zero_add_one

lemma NontrivialGood.map_one {S} [NonAssocSemiring S]
    {f : R → S} (hf : NontrivialGood f) : f 1 = 0 := by
  rw [← zero_add 1, ← zero_mul 0, hf.is_good, zero_add,
    ← add_one_mul (f 0), hf.map_zero_add_one, zero_mul]

structure ReducedGood (f : R → S) extends NontrivialGood f where
  period_imp_eq (c d) (_ : ∀ x, f (x + c) = f (x + d)) : c = d

lemma ReducedGood.period_imp_zero {f : R → S} (hf : ReducedGood f)
    (h : ∀ x, f (x + c) = f x) : c = 0 :=
  hf.period_imp_eq c 0 λ x ↦ by rw [h, add_zero]
