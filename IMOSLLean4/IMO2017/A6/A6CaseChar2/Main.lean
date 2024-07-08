/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Basic
import Mathlib.Algebra.Field.Basic
import IMOSLLean4.Extra.CharTwo.Ring

/-!
# IMO 2017 A6 (P2, Solution to Case 2: Fields of characteristic 2)

We find all good functions `f : F → F` when `F` is a field of characteristic `2`.

### Extra notes

The proof of injectivity seems to generalize to units.
That is, given `char(R) = 2` and `f : R → R` reduced good,
  any `a, b ∈ Rˣ` with `f(a) = f(b)` satisfies `a = b`.
-/

namespace IMOSL
namespace IMO2017A6

open Extra

/-- `x ↦ x + 1` is an answer in characteristic 2 -/
theorem CharTwo_add_one_is_good [NonAssocRing R] [CharTwo R] : good (· + (1 : R)) := by
  simp only [add_comm _ (1 : R), ← Extra.CharTwo.sub_eq_add]; exact one_sub_is_good





/-! ### Good functions on division rings -/

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

end good





/-! ### Reduced good functions on fields of characteristic 2 -/

namespace ReducedGood

variable [Field F] [CharTwo F] {f : F → F} (hf : ReducedGood f)

theorem CharTwoField_map_zero_eq_one : f 0 = 1 :=
  CharTwo.mul_self_eq_one_iff.mp hf.map_zero_mul_self

theorem CharTwoField_map_add_one (x) : f (x + 1) = f x + 1 := by
  rw [hf.is_good.map_add_one, hf.CharTwoField_map_zero_eq_one, CharTwo.sub_eq_add]

theorem CharTwoField_map_eq_step1 (hb : b ≠ 0) (h : f a = f b) :
    f (a * b⁻¹ + (a + b⁻¹)) = f (1 + (a + b⁻¹)) := by
  have X : ∀ x, f (x + 1) = f x + 1 := hf.CharTwoField_map_add_one
  replace h : f (a + 1) = f (b + 1) := hf.is_good.map_add_one_eq_of_map_eq h
  have h0 := hf.is_good (a + 1) (b⁻¹ + 1)
  rwa [h, hf.is_good.DivRing_inv_formula hb, zero_add, add_one_mul a,
    mul_add_one a, add_right_comm, X, ← add_assoc (_ + _), X,
    add_left_inj, eq_comm, ← add_rotate', add_assoc] at h0

theorem CharTwoField_injective : f.Injective := λ a b h ↦ by
  have X : ∀ x, f (x + 1) = f x + 1 := hf.CharTwoField_map_add_one
  have X0 {c} : f c = 0 ↔ c = 1 := hf.map_eq_zero_iff
  have h0 : f 0 = 1 := hf.CharTwoField_map_zero_eq_one
  have h1 {c} : f c = 1 ↔ c = 0 := by
    rw [← CharTwo.add_eq_zero_iff_eq, ← X, X0, add_left_eq_self]
  -- First exclude the case `a = 0` and the case `b = 0`
  rcases eq_or_ne a 0 with rfl | ha
  · rwa [h0, eq_comm, h1, eq_comm] at h
  rcases eq_or_ne b 0 with rfl | hb
  · rwa [h0, h1] at h
  -- Now grind out the rest
  replace h0 : (a * b⁻¹ + (a + b⁻¹)) * (b * a⁻¹ + (b + a⁻¹))
      = (1 + (a + b⁻¹)) * (1 + (b + a⁻¹)) :=
    calc
    _ = (a * b⁻¹) * (b * a⁻¹) + (a * b⁻¹) * (b + a⁻¹)
        + ((a + b⁻¹) * (b * a⁻¹) + (a + b⁻¹) * (b + a⁻¹)) := by
      rw [add_mul, mul_add, mul_add (a + b⁻¹)]
    _ = 1 + (a + b⁻¹) + ((b + a⁻¹) + (a + b⁻¹) * (b + a⁻¹)) := by
      have h2 {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) : (c * d⁻¹) * (d + c⁻¹) = c + d⁻¹ := by
        rw [mul_add, inv_mul_cancel_right₀ hd, mul_rotate, inv_mul_cancel_right₀ hc]
      refine congrArg₂ _ (congrArg₂ _ ?_ (h2 ha hb)) (congrArg₂ _ ?_ rfl)
      · rw [mul_assoc, inv_mul_cancel_left₀ hb, mul_inv_cancel ha]
      · rw [mul_comm, h2 hb ha]
    _ = _ := by rw [mul_one_add (α := F), one_add_mul (α := F)]
  replace h0 : f (a * b⁻¹ + (a + b⁻¹) + (b * a⁻¹ + (b + a⁻¹)))
      = f (1 + (a + b⁻¹) + (1 + (b + a⁻¹))) := by
    have h2 := hf.CharTwoField_map_eq_step1 hb h
    have h3 := hf.CharTwoField_map_eq_step1 ha h.symm
    rw [eq_sub_of_add_eq' (hf.is_good _ _), h2, h3, h0]
    exact (eq_sub_of_add_eq' (hf.is_good _ _)).symm
  replace h : (a + b + 1) * (b⁻¹ + a⁻¹ + 1) + 1
      = a * b⁻¹ + (a + b⁻¹) + (b * a⁻¹ + (b + a⁻¹)) :=
    calc
    _ = (a + b) * (b⁻¹ + a⁻¹) + ((a + b) + (b⁻¹ + a⁻¹)) := by
      rw [add_one_mul (a + b), mul_add_one (a + b), add_assoc, add_assoc,
        CharTwo.add_add_cancel_right, ← add_assoc (a + b), ← add_assoc]
    _ = (a * b⁻¹ + b * a⁻¹) + ((a + b⁻¹) + (b + a⁻¹)) := by
      refine congrArg₂ _ ?_ (add_add_add_comm _ _ _ _)
      rw [add_mul, mul_add, mul_add, mul_inv_cancel ha,
        mul_inv_cancel hb, ← add_assoc, CharTwo.add_add_cancel_right]
    _ = _ := by rw [add_add_add_comm]
  rw [← h, X, add_add_add_comm, add_add_add_comm a, add_add_add_comm, add_comm 1, add_comm 1,
    ← hf.is_good, CharTwo.add_eq_iff_eq_add', add_left_inj, h1, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · rwa [X0, add_left_eq_self, CharTwo.add_eq_zero_iff_eq] at h0
  · rwa [X0, add_left_eq_self, CharTwo.add_eq_zero_iff_eq, inv_inj, eq_comm] at h0

theorem CharTwoField_solution : f = (· + 1) :=
  funext λ x ↦ by rw [hf.is_good.solution_of_injective hf.CharTwoField_injective,
    hf.CharTwoField_map_zero_eq_one, one_mul, CharTwo.sub_eq_add, add_comm]

end ReducedGood





/-! ### Final solution for `char(F) = 2` -/

/-- Final solution for fields of characteristic `2` -/
theorem CharTwoField_good_iff [Field F] [CharTwo F] {f : F → F} :
    good f ↔ f = 0 ∨ f = (· + 1) :=
  ⟨λ hf ↦ hf.DivRing_zero_or_reduced.imp_right ReducedGood.CharTwoField_solution,
  λ hf ↦ by rcases hf with rfl | rfl; exacts [zero_is_good, CharTwo_add_one_is_good]⟩
