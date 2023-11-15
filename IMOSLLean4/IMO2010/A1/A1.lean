/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Floor

/-! # IMO 2010 A1 (P1) -/

namespace IMOSL
namespace IMO2010A1

/-- Final solution -/
theorem final_solution {F : Type _} [LinearOrderedField F] [FloorRing F]
  {R : Type _} [LinearOrderedRing R] [FloorRing R] (f : F → R) :
    (∀ x y : F, f (⌊x⌋ * y) = f x * ⌊f y⌋) ↔
      (∃ C : R, ⌊C⌋ = 1 ∧ f = λ _ ↦ C) ∨ f = 0 := by
  constructor <;> intro h
  ---- `→`
  · have h0 := h 0 0
    rw [mul_zero, eq_comm, mul_right_eq_self₀] at h0
    apply h0.imp <;> intro h0
    -- Case 1: `⌊f(0)⌋ = 1`
    · refine ⟨f 0, Int.cast_eq_one.mp h0, funext λ x ↦ ?_⟩
      rw [← mul_one (f x), ← h0, ← h, mul_zero]
    -- Case 2: `f(0) = 0`
    · -- Start with `⌊f(1/2)⌋ = 0`
      have h1 : ⌊(2 : F)⁻¹⌋ = 0 := Int.floor_eq_zero_iff.mpr
        ⟨inv_nonneg.mpr zero_le_two, inv_lt_one one_lt_two⟩
      have h2 := h 2⁻¹ 2⁻¹
      rw [h1, Int.cast_zero, zero_mul, h0, zero_eq_mul, Int.cast_eq_zero] at h2
      replace h2 : ⌊f 2⁻¹⌋ = 0 := h2.elim (λ h3 ↦ by rw [h3, Int.floor_zero]) id
      -- Now get `f(1) = 0`
      replace h1 := h ((2 : ℤ) : F) 2⁻¹
      rw [h2, Int.cast_zero, mul_zero, Int.floor_intCast,
        Int.cast_two, mul_inv_cancel two_ne_zero] at h1
      -- Finally get `f = 0`
      ext y
      specialize h 1 y
      rwa [h1, zero_mul, Int.floor_one, Int.cast_one, one_mul] at h
  ---- `←`
  · intros x y
    rcases h with ⟨C, h, rfl⟩ | rfl
    · rw [h, Int.cast_one, mul_one]
    · exact (zero_mul _).symm

end IMO2010A1
end IMOSL
