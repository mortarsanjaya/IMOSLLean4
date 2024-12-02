/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Lemmas.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors


/-!
# IMO 2017 A6 (P2, Solution to reduced version with `2 ∈ R⁰`)

We find all reduced good functions `f : R → R` when `2 ∈ R⁰`.
Here, `R⁰` is the set of non-zero-divisors of `R`.
-/

namespace IMOSL
namespace IMO2017A6

open scoped nonZeroDivisors

variable [Ring R] (hR : 2 ∈ R⁰) [FunLike F R R] [NonperiodicGoodFunClass F R] (f : F)
include hR

theorem eq_zero_of_map_neg_eq_of_map_eq (h : f (-x) = f x) : x = 0 := by
  have h0 : f (-1) = f 0 + f 0 := by rw [← map_sub_one, zero_sub]
  have h1 : f (f x * f 0 * 2) + f 0 = 0 := by
    have h1 := good_def f x (-1)
    rwa [h0, ← mul_two, ← mul_assoc, mul_neg_one x, h, ← sub_eq_add_neg,
      map_sub_one, add_left_comm, add_right_eq_self] at h1
  replace h1 : f x * f 0 = 1 := by
    rwa [← map_sub_one, map_eq_zero_iff, sub_eq_iff_eq_add,
      ← mul_two, mul_cancel_right_mem_nonZeroDivisors hR] at h1
  replace h1 : f x = f 0 := by
    replace h1 : (f x * f 0) * f 0 = 1 * f 0 := congrArg₂ _ h1 rfl
    rwa [one_mul, mul_assoc, map_zero_mul_self, mul_one] at h1
  rwa [← sub_eq_zero, ← map_add_one, map_eq_zero_iff, add_left_eq_self] at h1

theorem NZD2_injective : (f : R → R).Injective := λ c d h ↦ by
  rw [← add_right_cancel_iff (a := -d), add_neg_cancel]
  apply eq_zero_of_map_neg_eq_of_map_eq hR f
  ---- Now focus on proving that `f(c - d) = f(d - c)`
  have h0 : f (-c) = f (-d) := map_neg_eq_of_map_eq h
  have h1 : f (c * d) = f (d * c) := by rw [← good_def, ← good_def f d, h, add_comm c]
  replace h1 : f (-(c * d)) = f (-(d * c)) := map_neg_eq_of_map_eq h1
  have h2 := good_def f c (-d)
  rw [mul_neg, h1, h, ← h0, ← mul_neg, ← good_def f d, add_right_inj] at h2
  rw [h2, neg_add_rev, neg_neg]

theorem NZD2_map_zero_mul_self : f 0 * f 0 = 1 :=
  map_zero_mul_self_of_injective (NZD2_injective hR f)

theorem NZD2_solution : ∀ x, f x = f 0 * (1 - x) :=
  solution_of_injective (NZD2_injective hR f)

theorem NZD2_map_zero_comm : ∀ x, f 0 * x = x * f 0 :=
  map_zero_comm_of_injective (NZD2_injective hR f)
