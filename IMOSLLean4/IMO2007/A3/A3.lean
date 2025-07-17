/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.GeomSum

/-!
# IMO 2007 A3

Let $F$ be a totally ordered field, and let $n$ be a positive integer.
Let $x, y ∈ F$ be positive elements such that $x^n + y^n = 1$.
Prove that
$$ \left(\sum_{k = 1}^n \frac{1 + x^{2k}}{1 + x^{4k}}\right)
  \left(\sum_{k = 1}^n \frac{1 + y^{2k}}{1 + y^{4k}}\right)
  < \frac{1}{(1 - x)(1 - y)}. $$
-/

namespace IMOSL
namespace IMO2007A3

open Finset

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem easy_ineq (x : F) : 0 ≤ (1 + x ^ 2) / (1 + x ^ 4) :=
  div_nonneg (add_nonneg zero_le_one (sq_nonneg x))
    (add_nonneg zero_le_one ((even_two_mul 2).pow_nonneg x))

theorem sum_easy_ineq (x : F) (S : Finset ℕ) :
    0 ≤ S.sum λ i ↦ (1 + x ^ (2 * i.succ)) / (1 + x ^ (4 * i.succ)) :=
  sum_nonneg λ i _ ↦ by rw [mul_comm, pow_mul, mul_comm, pow_mul]; exact easy_ineq _

theorem main_ineq {x : F} (h : 0 < x) (h0 : x ≠ 1) : (1 + x ^ 2) / (1 + x ^ 4) < x⁻¹ := by
  rw [inv_eq_one_div, div_lt_div_iff₀ (add_pos one_pos (pow_pos h 4)) h, one_mul,
    ← sub_pos, one_add_mul _ x, ← pow_succ, pow_succ, add_sub_add_comm,
    add_comm, ← mul_sub_one, ← neg_sub x, ← sub_eq_add_neg, ← sub_one_mul]
  have h1 : 3 ≠ 0 := Nat.succ_ne_zero 2
  obtain (h0 | h0) : 1 < x ∨ x < 1 := lt_or_gt_of_ne h0.symm
  exacts [mul_pos (sub_pos.mpr (one_lt_pow₀ h0 h1)) (sub_pos.mpr h0),
    mul_pos_of_neg_of_neg (sub_neg.mpr (pow_lt_one₀ h.le h0 h1)) (sub_neg.mpr h0)]

theorem sum_main_ineq {x : F} (h : 0 < x) (h0 : x < 1) (h1 : 0 < n) :
    (range n).sum (λ i ↦ (1 + x ^ (2 * i.succ)) / (1 + x ^ (4 * i.succ)))
      < (1 - x ^ n) / (x ^ n * (1 - x)) := calc
  _ < (range n).sum (λ i ↦ x⁻¹ ^ i * x⁻¹) := by
    refine sum_lt_sum_of_nonempty ⟨0, mem_range.mpr h1⟩ λ i _ ↦ ?_
    rw [mul_comm, pow_mul, mul_comm, pow_mul, ← pow_succ, inv_pow]
    exact main_ineq (pow_pos h _) (pow_lt_one₀ h.le h0 i.succ_ne_zero).ne
  _ = (1 - x ^ n) / (x ^ n * (1 - x)) := by
    rw [← sum_mul, geom_sum_eq (λ h2 ↦ h0.ne (inv_eq_one.mp h2)), ← div_eq_mul_inv,
      div_div, sub_one_mul, ← div_div, div_eq_mul_inv _ (x ^ n), one_sub_mul,
      ← inv_pow, ← mul_pow, mul_comm, mul_inv_cancel₀ h.ne.symm, one_pow]

/-- Final solution -/
theorem final_solution {x y : F} (hx : 0 < x) (hy : 0 < y) (h : x ^ n + y ^ n = 1) :
    (range n).sum (λ i ↦ (1 + x ^ (2 * i.succ)) / (1 + x ^ (4 * i.succ)))
      * (range n).sum (λ i ↦ (1 + y ^ (2 * i.succ)) / (1 + y ^ (4 * i.succ)))
      < ((1 - x) * (1 - y))⁻¹ := calc
  _ < (1 - x ^ n) / (x ^ n * (1 - x)) * ((1 - y ^ n) / (y ^ n * (1 - y))) := by
    obtain (rfl | hn) : n = 0 ∨ 0 < n := n.eq_zero_or_pos
    · rw [pow_zero, pow_zero, add_eq_left] at h
      exact absurd h one_ne_zero
    have X (a b : F) (hb : 0 < b) (h : a ^ n + b ^ n = 1) : a < 1 :=
      lt_of_not_ge λ h1 ↦ h.not_gt (lt_add_of_le_of_pos (one_le_pow₀ h1) (pow_pos hb n))
    exact mul_lt_mul'' (sum_main_ineq hx (X x y hy h) hn)
      (sum_main_ineq hy (X y x hx ((add_comm _ _).trans h)) hn)
      (sum_easy_ineq _ _) (sum_easy_ineq _ _)
  _ = ((1 - x) * (1 - y))⁻¹ := by
    rw [← eq_sub_of_add_eq h, ← eq_sub_of_add_eq' h, div_mul_div_comm, mul_mul_mul_comm,
      mul_comm, ← mul_pow, div_mul_cancel_left₀ (pow_ne_zero _ (mul_pos hx hy).ne.symm)]
