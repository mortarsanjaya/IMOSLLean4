/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Lemmas.Basic
import Mathlib.Algebra.Field.Defs

/-!
# IMO 2017 A6 (P2, Good functions over a division ring)

We prove that non-zero good functions over a division ring are reduced good.
-/

namespace IMOSL
namespace IMO2017A6

variable [DivisionRing R]

section

variable [FunLike F R R] [GoodFunClass F R] (f : F)

/-- Good functions on division rings: a formula -/
theorem DivRing_inv_formula {c : R} (h : c ≠ 0) : f (f (c + 1) * f (c⁻¹ + 1)) = 0 := by
  rw [eq_sub_of_add_eq (good_def f _ _), sub_eq_zero, add_one_mul c,
    mul_add_one c, mul_inv_cancel₀ h, add_comm 1]

/-- Good functions on division rings: either `0` or reduced -/
theorem DivRing_zero_or_reduced : (∀ x, f x = 0) ∨ nonperiodicGood f := by
  apply (em (∃ c, c ≠ 0 ∧ f (c + 1) = 0)).imp
  -- Case 1: `f(c + 1) = 0` for some `c ≠ 0`
  · rintro ⟨c, h, h0⟩
    have h1 := DivRing_inv_formula f h
    rw [h0, zero_mul] at h1
    intro x; have h2 := map_map_zero_mul_map f x
    rwa [h1, zero_mul, h1, zero_add] at h2
  -- Case 2: `f(c + 1) = 0 ↔ c = 0`
  · intro h; refine ⟨⟨GoodFunClass.toGoodFun f,
      λ c d (h0 : ∀ x, f (x + c) = f (x + d)) ↦ ?_⟩, rfl⟩
    refine eq_of_sub_eq_zero (by_contra λ h1 ↦ h ⟨_, h1, ?_⟩)
    replace h0 (x) : f (x + c) = f (x + d) := h0 x
    rw [sub_add_comm, h0, sub_add_cancel, map_one_eq_zero]

end

/-- The `↔` version of `DivRing_zero_or_reduced` -/
theorem DivRing_iff_zero_or_reduced {f : R → R} :
    good f ↔ (f = λ _ ↦ 0) ∨ nonperiodicGood f := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩; exact (DivRing_zero_or_reduced f).imp_left funext
  · rintro (rfl | ⟨f, rfl⟩)
    · exact ⟨GoodFun_zero R, rfl⟩
    · exact ⟨f.toGoodFun, rfl⟩
