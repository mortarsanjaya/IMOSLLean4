/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Basic
import Mathlib.Algebra.Group.Invertible.Defs

/-!
# IMO 2017 A6 (P2, Solution to reduced version of Case 1: `2 ∈ Rˣ`)

We find all reduced good functions `f : R → R` when `2 ∈ Rˣ`.

### Extra notes

The same proof works whenever `2` is not a zero divisor.
However, we need `2` to be invertible in `R` for the original problem to guarantee
  that taking quotient with any double-sided ideal does not make `2` a zero divisor.
-/

namespace IMOSL
namespace IMO2017A6
namespace ReducedGood

variable [Ring R] [Invertible (2 : R)] {f : R → R} (hf : ReducedGood f)

theorem eq_zero_of_map_neg_eq_of_map_eq (h : f (-x) = f x) : x = 0 := by
  have h0 : f (-1) = f 0 + f 0 := by rw [← hf.is_good.map_sub_one, zero_sub]
  have h1 : f (f x * f 0 * 2) + f 0 = 0 := by
    have h1 := hf.is_good x (-1)
    rwa [h0, ← mul_two, ← mul_assoc, mul_neg_one x, h, ← sub_eq_add_neg,
      hf.is_good.map_sub_one, add_left_comm, add_right_eq_self] at h1
  replace h1 : f x * f 0 = 1 := by
    rwa [← hf.is_good.map_sub_one, hf.map_eq_zero_iff,
      sub_eq_iff_eq_add, ← mul_two, mul_right_inj_of_invertible] at h1
  replace h1 : f x = f 0 := by
    replace h1 : (f x * f 0) * f 0 = 1 * f 0 := congrArg₂ _ h1 rfl
    rwa [one_mul, mul_assoc, hf.map_zero_mul_self, mul_one] at h1
  rwa [← sub_eq_zero, ← hf.is_good.map_add_one, hf.map_eq_zero_iff, add_left_eq_self] at h1

theorem InvertibleTwo_injective : f.Injective := λ c d h ↦ by
  rw [← add_right_cancel_iff (a := -d), add_neg_self]
  apply hf.eq_zero_of_map_neg_eq_of_map_eq
  ---- Now focus on proving that `f(c - d) = f(d - c)`
  have h0 : f (-c) = f (-d) := hf.is_good.map_neg_eq_of_map_eq h
  have h1 : f (c * d) = f (d * c) := by rw [← hf.is_good, ← hf.is_good d, h, add_comm c]
  replace h1 : f (-(c * d)) = f (-(d * c)) := hf.is_good.map_neg_eq_of_map_eq h1
  have h2 := hf.is_good c (-d)
  rw [mul_neg, h1, h, ← h0, ← mul_neg, ← hf.is_good d, add_right_inj] at h2
  rw [h2, neg_add_rev, neg_neg]

/-
theorem InvertibleTwo_solution :
    ∃ a : R, (a * a = 1 ∧ ∀ x, a * x = x * a) ∧ f = λ x ↦ a * (1 - x) :=
  let X := hf.InvertibleTwo_injective
  ⟨f 0, ⟨hf.map_zero_mul_self, hf.is_good.map_zero_comm_of_injective X⟩,
    funext (hf.is_good.solution_of_injective X)⟩
-/
