/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat

/-!
# IMO 2006 A2

Consider the sequence $(a_n)_{n ≥ 0}$ of rational nuimbers defined by $a_0 = 1$ and
$$ a_n = -\sum_{k = 0}^{n - 1} \frac{a_k}{n + 1 - k}. $$
Prove that $a_n > 0$ for all $n ≠ 0$.
-/

namespace IMOSL
namespace IMO2006A2

open Finset

def a : ℕ → ℚ
  | 0 => -1
  | n + 1 => -(univ : Finset (Fin (n + 1))).sum λ i ↦ a i / (n + 2 - i : ℕ)

lemma a_zero : a 0 = -1 := by
  rw [a]

lemma a_succ (n) : a (n + 1) = -(range (n + 1)).sum λ i ↦ a i / (n + 2 - i : ℕ) := by
  rw [a, ← Fin.sum_univ_eq_sum_range]

lemma a_one : a 1 = 1 / 2 := by
  rw [a, Fin.sum_univ_one, Fin.val_zero, a, neg_div, neg_neg]; rfl

lemma a_nonzero (h : n ≠ 0) : a n = -(range n).sum λ i ↦ a i / (n + 1 - i : ℕ) :=
  Nat.succ_pred_eq_of_ne_zero h ▸ a_succ n.pred

lemma a_nonzero' (h : n ≠ 0) : (range (n + 1)).sum (λ i ↦ a i / (n + 1 - i : ℕ)) = 0 := by
  rw [sum_range_succ, ← neg_eq_iff_add_eq_zero, ← a_nonzero h,
    Nat.add_sub_cancel_left, Rat.div_def, Rat.inv_def]
  exact (a n).mul_one.symm

lemma Rat_formula {k n : ℕ} (h : k < n) :
    (n : ℚ) / (n - k : ℕ) - (n + 1 : ℕ) / (n + 1 - k : ℕ)
      = k / ((n - k) * (n + 1 - k) : ℕ) := by
  rw [lt_iff_exists_add] at h; rcases h with ⟨c, h, rfl⟩
  rw [gt_iff_lt, ← Nat.ne_zero_iff_zero_lt] at h
  rw [Nat.add_sub_cancel_left, Nat.add_assoc, Nat.add_sub_cancel_left, Nat.cast_mul,
    div_sub_div _ _ (Nat.cast_ne_zero.mpr h) (Nat.cast_ne_zero.mpr c.succ_ne_zero)]
  refine congrArg₂ _ ?_ rfl
  rw [k.cast_add, k.cast_add, add_mul, mul_add, add_sub_add_right_eq_sub,
    mul_comm, Nat.cast_succ, add_one_mul (c : ℚ), add_sub_cancel_left]

lemma a_formula (h : n ≠ 0) :
    (n + 2 : ℕ) * a (n + 1) =
      (range (n + 1)).sum λ i ↦ a i * (i / ((n + 1 - i) * (n + 2 - i) : ℕ)) :=
  calc
  _ = (n + 1 : ℕ) * (range (n + 1)).sum (λ i ↦ a i / (n + 1 - i : ℕ))
      - (n + 2 : ℕ) * (range (n + 1)).sum (λ i ↦ a i / (n + 2 - i : ℕ)) := by
    rw [a_nonzero' h, Rat.mul_zero, zero_sub, a_nonzero n.succ_ne_zero, mul_neg]
  _ = (range (n + 1)).sum λ i ↦
      (n + 1 : ℕ) * (a i / (n + 1 - i : ℕ)) - (n + 2 : ℕ) * (a i / (n + 2 - i : ℕ)) := by
    rw [sum_sub_distrib, mul_sum, mul_sum]
  _ = _ := sum_congr rfl λ i h0 ↦ by
    rw [mul_div_left_comm, mul_div_left_comm _ (a i),
      ← mul_sub, Rat_formula (mem_range.mp h0)]



/-- Final solution -/
theorem final_solution (h : n ≠ 0) : 0 < a n := by
  induction' n using Nat.strong_induction_on with n h0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  clear h; rcases eq_or_ne n 0 with rfl | h
  ---- `a_1 > 0`
  · exact (div_pos one_pos two_pos).trans_eq a_one.symm
  ---- If `a_i > 0` for all `0 < i ≤ n`, then `a_{n + 1} > 0`
  · refine pos_of_mul_pos_right ?_ (n + 2).cast_nonneg
    rw [a_formula h, sum_range_succ', Nat.cast_zero, zero_div, mul_zero, add_zero]
    refine sum_pos (λ i h1 ↦ ?_) (nonempty_range_iff.mpr h)
    rw [mem_range] at h1
    refine mul_pos (h0 i.succ (Nat.succ_lt_succ h1) i.succ_ne_zero)
      (div_pos (Nat.cast_pos.mpr i.succ_pos) (Nat.cast_pos.mpr ?_))
    rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
    exact Nat.mul_pos (Nat.sub_pos_of_lt h1) (Nat.sub_pos_of_lt (Nat.lt_add_right 1 h1))
