/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Lemmas.Field
import IMOSLLean4.IMO2017.A6.A6Lemmas.ReducedNZD2
import IMOSLLean4.Extra.CharTwo.Ring
import Mathlib.Algebra.Ring.Commute

/-!
# IMO 2017 A6 (P2, Solution to the case: `R` is a field)

We find all good functions `f : F → F` when `F` is a field.
We solve more: if `char(F) ≠ 2`, then `F` can be a division ring.

### Extra notes

The proof of injectivity seems to generalize to units.
That is, given `char(R) = 2` and `f : R → R` reduced good,
  any `a, b ∈ Rˣ` with `f(a) = f(b)` satisfies `a = b`.
-/

namespace IMOSL
namespace IMO2017A6

open Extra

section

/-! ### Reduced good functions on fields of characteristic 2 -/

variable [Field R] [CharTwo R] [FunLike F R R] [NonperiodicGoodFunClass F R] (f : F)

theorem CharTwoField_map_zero_eq_one : f 0 = 1 :=
  CharTwo.mul_self_eq_one_iff.mp (map_zero_mul_self f)

theorem CharTwoField_map_add_one (x) : f (x + 1) = f x + 1 := by
  rw [map_add_one, CharTwoField_map_zero_eq_one, CharTwo.sub_eq_add]

theorem CharTwoField_map_eq_step1 (hb : b ≠ 0) (h : f a = f b) :
    f (a * b⁻¹ + (a + b⁻¹)) = f (1 + (a + b⁻¹)) := by
  have X : ∀ x, f (x + 1) = f x + 1 := CharTwoField_map_add_one f
  replace h : f (a + 1) = f (b + 1) := map_add_one_eq_of_map_eq h
  have h0 := good_def f (a + 1) (b⁻¹ + 1)
  rwa [h, DivRing_inv_formula f hb, zero_add, add_one_mul a,
    mul_add_one a, add_right_comm, X, ← add_assoc (_ + _), X,
    add_left_inj, eq_comm, ← add_rotate', add_assoc] at h0

theorem CharTwoField_injective : (f : R → R).Injective := λ a b h ↦ by
  have X : ∀ x, f (x + 1) = f x + 1 := CharTwoField_map_add_one f
  have X0 {c} : f c = 0 ↔ c = 1 := map_eq_zero_iff
  have h0 : f 0 = 1 := CharTwoField_map_zero_eq_one f
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
      have h2 {c d : R} (hc : c ≠ 0) (hd : d ≠ 0) : (c * d⁻¹) * (d + c⁻¹) = c + d⁻¹ := by
        rw [mul_add, inv_mul_cancel_right₀ hd, mul_rotate, inv_mul_cancel_right₀ hc]
      refine congrArg₂ _ (congrArg₂ _ ?_ (h2 ha hb)) (congrArg₂ _ ?_ rfl)
      · rw [mul_assoc, inv_mul_cancel_left₀ hb, mul_inv_cancel₀ ha]
      · rw [mul_comm, h2 hb ha]
    _ = _ := by rw [mul_one_add (α := R), one_add_mul (α := R)]
  replace h0 : f (a * b⁻¹ + (a + b⁻¹) + (b * a⁻¹ + (b + a⁻¹)))
      = f (1 + (a + b⁻¹) + (1 + (b + a⁻¹))) := by
    have h2 := CharTwoField_map_eq_step1 f hb h
    have h3 := CharTwoField_map_eq_step1 f ha h.symm
    rw [eq_sub_of_add_eq' (good_def f _ _), h2, h3, h0]
    exact (eq_sub_of_add_eq' (good_def f _ _)).symm
  replace h : (a + b + 1) * (b⁻¹ + a⁻¹ + 1) + 1
      = a * b⁻¹ + (a + b⁻¹) + (b * a⁻¹ + (b + a⁻¹)) :=
    calc
    _ = (a + b) * (b⁻¹ + a⁻¹) + ((a + b) + (b⁻¹ + a⁻¹)) := by
      rw [add_one_mul (a + b), mul_add_one (a + b), add_assoc, add_assoc,
        CharTwo.add_add_cancel_right, ← add_assoc (a + b), ← add_assoc]
    _ = (a * b⁻¹ + b * a⁻¹) + ((a + b⁻¹) + (b + a⁻¹)) := by
      refine congrArg₂ _ ?_ (add_add_add_comm _ _ _ _)
      rw [add_mul, mul_add, mul_add, mul_inv_cancel₀ ha,
        mul_inv_cancel₀ hb, ← add_assoc, CharTwo.add_add_cancel_right]
    _ = _ := by rw [add_add_add_comm]
  rw [← h, X, add_add_add_comm, add_add_add_comm a, add_add_add_comm, add_comm 1, add_comm 1,
    ← good_def, CharTwo.add_eq_iff_eq_add', add_left_inj, h1, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · rwa [X0, add_left_eq_self, CharTwo.add_eq_zero_iff_eq] at h0
  · rwa [X0, add_left_eq_self, CharTwo.add_eq_zero_iff_eq, inv_inj, eq_comm] at h0

theorem CharTwoField_solution (x) : f x = 1 - x := by
  rw [solution_of_injective (CharTwoField_injective f),
    CharTwoField_map_zero_eq_one, one_mul]

end





/-! ### Final solution for field case -/

/-- Final solution for fields of characteristic `2` -/
theorem CharTwoField_good_iff [Field F] [CharTwo F] {f : F → F} :
    good f ↔ f = 0 ∨ f = λ x ↦ 1 - x := by
  refine DivRing_iff_zero_or_reduced.trans (or_congr_right ⟨?_, ?_⟩)
  · rintro ⟨f, rfl⟩; exact funext (CharTwoField_solution f)
  · rintro rfl; exact ⟨NonperiodicGoodFun_one_sub F, rfl⟩

/-- Final solution for division rings with `2 ≠ 0` -/
theorem CharNeTwoDivRing_good_iff [DivisionRing F] [hR : NeZero (2 : F)] {f : F → F} :
    good f ↔ f = 0 ∨ f = (1 - ·) ∨ f = (· - 1) := by
  refine DivRing_iff_zero_or_reduced.trans (or_congr_right ?_)
  refine ⟨λ hf ↦ ?_, ?_⟩
  · rcases hf with ⟨f, rfl⟩
    have h := NZD2_solution (mem_nonZeroDivisors_of_ne_zero two_ne_zero) f
    refine (mul_self_eq_one_iff.mp (map_zero_mul_self f)).imp (λ h0 ↦ ?_) (λ h0 ↦ ?_)
    · funext x; change f x = 1 - x; rw [h, h0, one_mul]
    · funext x; change f x = x - 1; rw [h, h0, neg_one_mul, neg_sub]
  · rintro (rfl | rfl)
    · exact ⟨NonperiodicGoodFun_one_sub F, rfl⟩
    · exact ⟨NonperiodicGoodFun_sub_one F, rfl⟩

/-- Final solution for arbitrary fields -/
theorem Field_good_iff [Field F] {f : F → F} :
    good f ↔ f = 0 ∨ f = (1 - ·) ∨ f = (· - 1) := by
  by_cases h : (2 : F) = 0
  · haveI : CharTwo F := CharTwo.Semiring_of_two_eq_zero h
    rw [CharTwoField_good_iff]
    simp only [CharTwo.sub_eq_add', add_comm (1 : F)]
    rw [or_self]
  · haveI : NeZero (2 : F) := ⟨h⟩
    exact CharNeTwoDivRing_good_iff
