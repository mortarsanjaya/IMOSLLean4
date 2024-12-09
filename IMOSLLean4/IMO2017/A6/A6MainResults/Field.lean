/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Lemmas.Field
import IMOSLLean4.Extra.CharTwo.Ring
import Mathlib.Algebra.Ring.Commute

/-!
# IMO 2017 A6 (P2, Solution to the case: `R` is a field)

We find all $ι$-good functions $f : R → S$ when $R$ is a field.

### Extra notes

The proof of injectivity seems to generalize to units.
That is, given $char(R) = 2$ and $f : R → S$ non-periodic good,
  any $a, b ∈ Rˣ$ with $f(a) = f(b)$ satisfies $a = b$.
-/

namespace IMOSL
namespace IMO2017A6

open Extra

section

variable [Field R] [CharTwo R] [FunLike F R R]
  [NonperiodicGoodFunClass F (AddMonoidHom.id R)] (f : F)

theorem CharTwoField_map_zero_eq_one : f 0 = 1 :=
  CharTwo.mul_self_eq_one_iff.mp (incl_map_zero_mul_self (AddMonoidHom.id R) f)

theorem CharTwoField_map_add_one (x) : f (x + 1) = f x + 1 := by
  rw [map_add_one (AddMonoidHom.id R), CharTwoField_map_zero_eq_one, CharTwo.sub_eq_add]

theorem CharTwoField_map_eq_step1 (hb : b ≠ 0) (h : f a = f b) :
    f (a * b⁻¹ + (a + b⁻¹)) = f (1 + (a + b⁻¹)) := by
  have X : ∀ x, f (x + 1) = f x + 1 := CharTwoField_map_add_one f
  replace h : f (a + 1) = f (b + 1) := map_add_one_eq_of_map_eq (AddMonoidHom.id R) h
  have h0 := good_def (AddMonoidHom.id R) f (a + 1) (b⁻¹ + 1)
  rwa [h, DivRing_inv_formula (AddMonoidHom.id R) f hb, zero_add,
    add_one_mul a, mul_add_one a, add_right_comm, X, ← add_assoc (_ + _),
    X, add_left_inj, eq_comm, ← add_rotate', add_assoc] at h0

theorem CharTwoField_injective : (f : R → R).Injective := λ a b h ↦ by
  have X : ∀ x, f (x + 1) = f x + 1 := CharTwoField_map_add_one f
  have X0 {c} : f c = 0 ↔ c = 1 := map_eq_zero_iff (AddMonoidHom.id R)
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
    _ = _ := by rw [mul_one_add, one_add_mul]
  replace h0 : f (a * b⁻¹ + (a + b⁻¹) + (b * a⁻¹ + (b + a⁻¹)))
      = f (1 + (a + b⁻¹) + (1 + (b + a⁻¹))) := by
    have h2 := CharTwoField_map_eq_step1 f hb h
    have h3 := CharTwoField_map_eq_step1 f ha h.symm
    rw [eq_sub_of_add_eq' (good_def (AddMonoidHom.id R) f _ _), h2, h3, h0]
    exact (eq_sub_of_add_eq' (good_def (AddMonoidHom.id R) f _ _)).symm
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
  rw [← h, X, add_add_add_comm, add_add_add_comm a, add_add_add_comm, add_comm 1,
    add_comm 1, ← good_def (AddMonoidHom.id R), CharTwo.add_eq_iff_eq_add',
    add_left_inj, h1, mul_eq_zero, AddMonoidHom.id_apply, AddMonoidHom.id_apply] at h0
  rcases h0 with h0 | h0
  · rwa [X0, add_left_eq_self, CharTwo.add_eq_zero_iff_eq] at h0
  · rwa [X0, add_left_eq_self, CharTwo.add_eq_zero_iff_eq, inv_inj, eq_comm] at h0

theorem CharTwoField_solution (f : F) (x) : f x = x + 1 := by
  refine (solution_of_injective (AddMonoidHom.id R) (CharTwoField_injective f) x).trans ?_
  rw [CharTwoField_map_zero_eq_one, AddMonoidHom.id_apply,
    one_mul, CharTwo.sub_eq_add, add_comm]

end
