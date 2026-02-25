/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Basic

/-!
# IMO 2007 A3

Let $F$ be a totally ordered field, and let $n$ be a positive integer.
Let $x, y ∈ F$ be positive elements such that $x^n + y^n = 1$.
Prove that
$$ \left(\sum_{k = 1}^n \frac{1 + x^{2k}}{1 + x^{4k}}\right)
  \left(\sum_{k = 1}^n \frac{1 + y^{2k}}{1 + y^{4k}}\right)
  < \frac{1}{(1 - x)(1 - y)}. $$

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2007SL.pdf).
-/

namespace IMOSL
namespace IMO2007A3

open Finset

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The inequality `(1 + x^2)/(1 + x^4) ≥ 0`. -/
theorem easy_ineq (x : F) : 0 ≤ (1 + x ^ 2) / (1 + x ^ 4) :=
  div_nonneg (add_nonneg zero_le_one (sq_nonneg x))
    (add_nonneg zero_le_one ((even_two_mul 2).pow_nonneg x))

/-- The inequality `∑_{i ∈ S} (1 + x^{2i})/(1 + x^{4i}) ≥ 0`. -/
theorem sum_easy_ineq (x : F) (S : Finset ℕ) :
    0 ≤ ∑ i ∈ S, (1 + x ^ (2 * i)) / (1 + x ^ (4 * i)) := by
  refine sum_nonneg λ i _ ↦ ?_
  iterate 2 rw [mul_comm, pow_mul]
  exact easy_ineq _

/-- The inequality `(1 + x^2)/(1 + x^4) < 1/x` for `0 < x < 1`.
  Note that this inequality also holds for `x > 1`. -/
theorem main_ineq {x : F} (hx : 0 < x) (hx0 : x < 1) : (1 + x ^ 2) / (1 + x ^ 4) < x⁻¹ := by
  have h : 3 ≠ 0 := Nat.succ_ne_zero 2
  replace hx0 : 0 < (x ^ 3 - 1) * (x - 1) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr (pow_lt_one₀ hx.le hx0 h)) (sub_neg.mpr hx0)
  replace hx0 : 0 < (x ^ 3 * x + 1) - (x + x ^ 3) := by
    rwa [mul_sub_one, sub_one_mul, sub_sub_sub_eq] at hx0
  replace hx0 : (1 + x ^ 2) * x < 1 + x ^ 4 :=
    calc (1 + x ^ 2) * x
    _ = x + x ^ 3 := by rw [one_add_mul, ← pow_succ]
    _ < x ^ 3 * x + 1 := sub_pos.mp hx0
    _ = 1 + x ^ 4 := by rw [← pow_succ, add_comm]
  rwa [inv_eq_one_div, div_lt_div_iff₀ (add_pos one_pos (pow_pos hx 4)) hx, one_mul]

/-- The inequality `∑_{1 ≤ i ≤ n} (1 + x^{2i})/(1 + x^{4i}) < (1 - x^n)/(x^n (1 - x))`. -/
theorem sum_main_ineq {x : F} (hx : 0 < x) (hx0 : x < 1) (hx1 : 0 < n) :
    ∑ i ∈ Icc 1 n, (1 + x ^ (2 * i)) / (1 + x ^ (4 * i))
        < (1 - x ^ n) / (x ^ n * (1 - x)) :=
  have hx2 : x ≠ 0 := hx.ne.symm
  calc ∑ i ∈ Icc 1 n, (1 + x ^ (2 * i)) / (1 + x ^ (4 * i))
    _ < ∑ i ∈ Icc 1 n, x⁻¹ ^ i := by
      refine sum_lt_sum_of_nonempty (nonempty_Icc.mpr hx1) (λ i hi ↦ ?_)
      replace hi : i ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hi).1
      rw [mul_comm, pow_mul, mul_comm, pow_mul, inv_pow]
      exact main_ineq (pow_pos hx _) (pow_lt_one₀ hx.le hx0 hi)
    _ = ∑ i ∈ range n, x⁻¹ ^ (1 + i) := by
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    _ = ∑ i ∈ range n, x⁻¹ * x⁻¹ ^ i :=
      sum_congr rfl λ _ _ ↦ by rw [Nat.add_comm, pow_succ']
    _ = x⁻¹ * ((x - 1)⁻¹ * (x - x⁻¹ ^ n * x)) := by
      rw [← mul_sum, geom_sum_inv hx0.ne hx2]
    _ = (x - 1)⁻¹ * (1 - x⁻¹ ^ n) := by
      rw [mul_left_comm, ← one_sub_mul, mul_comm _ x, inv_mul_cancel_left₀ hx2]
    _ = (x⁻¹ ^ n - 1) / (1 - x) := by
      rw [inv_mul_eq_div, ← neg_div_neg_eq, neg_sub, neg_sub]
    _ = (1 - x ^ n) / (x ^ n * (1 - x)) := by
      rw [inv_pow, inv_eq_one_div, div_sub_one (pow_ne_zero _ hx2), div_div]

/-- Final solution -/
theorem final_solution {x y : F} (hx : 0 < x) (hy : 0 < y) (h : x ^ n + y ^ n = 1) :
    (∑ i ∈ Icc 1 n, (1 + x ^ (2 * i)) / (1 + x ^ (4 * i)))
        * ∑ i ∈ Icc 1 n, (1 + y ^ (2 * i)) / (1 + y ^ (4 * i))
      < 1 / ((1 - x) * (1 - y)) := calc
  _ < (1 - x ^ n) / (x ^ n * (1 - x)) * ((1 - y ^ n) / (y ^ n * (1 - y))) := by
    -- The case `n = 0` is contradictory to `x^n + y^n = 1`.
    obtain (rfl | hn) : n = 0 ∨ 0 < n := n.eq_zero_or_pos
    · rw [pow_zero, pow_zero, add_eq_left] at h
      exact absurd h one_ne_zero
    -- Otherwise we proceed normally.
    have X (a b : F) (hb : 0 < b) (h : a ^ n + b ^ n = 1) : a < 1 :=
      lt_of_not_ge λ h1 ↦ h.not_gt (lt_add_of_le_of_pos (one_le_pow₀ h1) (pow_pos hb n))
    exact mul_lt_mul'' (sum_main_ineq hx (X x y hy h) hn)
      (sum_main_ineq hy (X y x hx ((add_comm _ _).trans h)) hn)
      (sum_easy_ineq _ _) (sum_easy_ineq _ _)
  _ = y ^ n / (x ^ n * (1 - x)) * (x ^ n / (y ^ n * (1 - y))) := by
    rw [← eq_sub_of_add_eq h, ← eq_sub_of_add_eq' h]
  _ = (x ^ n * y ^ n) / ((x ^ n * y ^ n) * ((1 - x) * (1 - y))) := by
    rw [div_mul_div_comm, mul_mul_mul_comm, mul_comm]
  _ = 1 / ((1 - x) * (1 - y)) := by
    rw [← div_div, ← mul_pow, div_self (pow_pos (mul_pos hx hy) n).ne.symm]
