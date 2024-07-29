/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Lemmas.Basic
import Mathlib.Algebra.Field.Basic

/-!
# IMO 2017 A6 (P2, Good functions over a division ring)

We prove that non-zero good functions over a division ring are reduced good.
-/

namespace IMOSL
namespace IMO2017A6
namespace good

variable [DivisionRing F] {f : F → F} (hf : good f)

/-- Good functions on division rings: a formula -/
theorem DivRing_inv_formula {c : F} (h : c ≠ 0) : f (f (c + 1) * f (c⁻¹ + 1)) = 0 := by
  rw [eq_sub_of_add_eq (hf _ _), sub_eq_zero, add_one_mul c,
    mul_add_one c, mul_inv_cancel h, add_comm 1]

/-- Good functions on division rings: either `0` or reduced -/
theorem DivRing_zero_or_reduced : f = 0 ∨ ReducedGood f := by
  apply (em (∃ c, c ≠ 0 ∧ f (c + 1) = 0)).imp
  -- Case 1: `f(c + 1) = 0` for some `c ≠ 0`
  · rintro ⟨c, h, h0⟩
    have h1 := hf.DivRing_inv_formula h
    rw [h0, zero_mul] at h1
    funext x; have h2 := hf.map_map_zero_mul_map x
    rwa [h1, zero_mul, h1, zero_add] at h2
  -- Case 2: `f(c + 1) = 0 ↔ c = 0`
  · refine λ h ↦ ⟨hf, λ c d h0 ↦ eq_of_sub_eq_zero (by_contra λ h1 ↦ h ⟨_, h1, ?_⟩)⟩
    rw [sub_add_comm, h0, sub_add_cancel, hf.map_one_eq_zero]

/-- The `↔` version of `DivRing_zero_or_reduced` -/
theorem DivRing_iff_zero_or_reduced : good f ↔ f = 0 ∨ ReducedGood f :=
  ⟨DivRing_zero_or_reduced, λ h ↦ h.elim (λ hf ↦ hf ▸ zero_is_good) ReducedGood.is_good⟩
