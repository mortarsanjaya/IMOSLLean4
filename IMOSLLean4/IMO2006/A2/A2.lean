/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# IMO 2006 A2

Let $F$ be a totally ordered field.
Consider the sequence $(a_n)_{n ≥ 0}$ of elements of $F$ defined by $a_0 = 1$ and
$$ a_n = -\sum_{k = 0}^{n - 1} \frac{a_k}{n + 1 - k}. $$
Prove that $a_{n + 1} ≥ 0$ for all $n ≥ 0$.

### Solution

We follow the official solution.
See [here](https://www.imo-official.org/problems/IMO2006SL.pdf.)
-/

namespace IMOSL
namespace IMO2006A2

open Finset

/-- The sequence `(a_n)_{n ≥ 0}`. -/
abbrev a (F) [Field F] : ℕ → F
  | 0 => -1
  | n + 1 => -∑ i : Fin (n + 1), a F i / (n + 2 - i : ℕ)


variable {F} [Field F]

/-- `a_0 = -1`. -/
lemma a_zero : a F 0 = -1 := rfl

/-- `a_{n + 1} = -∑ i ≤ n, a_i/(n + 2 - i)`. -/
lemma a_succ (n) : a F (n + 1) = -∑ i ∈ range (n + 1), a F i / (n + 2 - i : ℕ) := by
  rw [a, ← Fin.sum_univ_eq_sum_range]

/-- `a_1 = 1/2`. -/
lemma a_one : a F 1 = 2⁻¹ := by
  rw [a, Fin.sum_univ_one, Fin.val_zero, a_zero, neg_div, neg_neg, one_div]; rfl

/-- Recursive formula for `a_{n + 1}` across all `n > 0`. -/
lemma a_rec (hn : 0 < n) : ∑ i ∈ range (n + 1), a F i / (n + 1 - i : ℕ) = 0 := by
  rw [← Nat.succ_pred_eq_of_pos hn, sum_range_succ, add_eq_zero_iff_eq_neg',
    ← a_succ, Nat.add_sub_cancel_left, Nat.cast_one, div_one]

/-- Main formula for `a_{n + 1}` as a positive linear combination of `a_1, …, a_n`. -/
lemma main_formula (hn : 0 < n) :
    (n + 2 : ℕ) * a F (n + 1) =
      ∑ i ∈ range (n + 1), a F i * ((n + 1 : ℕ) / (n + 1 - i : ℕ)
        - (n + 2 : ℕ) / ((n + 2 - i) : ℕ)) := calc
  _ = (n + 1 : ℕ) * ∑ i ∈ range (n + 1), a F i / (n + 1 - i : ℕ)
      - (n + 2 : ℕ) * ∑ i ∈ range (n + 1), a F i / (n + 2 - i : ℕ) := by
    rw [a_rec hn, mul_zero, zero_sub, ← mul_neg, ← a_succ]
  _ = ∑ i ∈ range (n + 1), ((n + 1 : ℕ) * (a F i / (n + 1 - i : ℕ))
      - (n + 2 : ℕ) * (a F i / (n + 2 - i : ℕ))) := by
    rw [sum_sub_distrib, mul_sum, mul_sum]
  _ = _ := sum_congr rfl λ i h ↦ by simp only [mul_div_left_comm _ (a F i), mul_sub]


variable [LinearOrder F] [IsStrictOrderedRing F]

/-- We have `(n + 1)/(n + 1 - i) < n/(n - i)` if `0 < i < n`. -/
lemma coeff_pos (hi : 0 < i) (hin : i < n) :
    ((n + 1 : ℕ) / (n + 1 - i : ℕ) : F) < n / (n - i : ℕ) := by
  have h : 0 < ((n - i : ℕ) : F) := by rwa [Nat.cast_pos, Nat.sub_pos_iff_lt]
  have h0 : ((n - i : ℕ) : F) < (n + 1 - i : ℕ) :=
    Nat.cast_lt.mpr (Nat.sub_lt_sub_right hin.le n.lt_succ_self)
  calc
  _ = (1 : F) + (i : ℕ) / (n + 1 - i : ℕ) := by
    rw [one_add_div (h.trans h0).ne.symm, ← Nat.cast_add,
      Nat.sub_add_cancel (Nat.le_succ_of_le hin.le)]
  _ < (1 : F) + (i : ℕ) / (n - i : ℕ) :=
    add_lt_add_left (div_lt_div_of_pos_left (Nat.cast_pos.mpr hi) h h0) 1
  _ = _ := by rw [one_add_div h.ne.symm, ← Nat.cast_add, Nat.sub_add_cancel hin.le]

/-- Final solution -/
theorem final_solution (n) : 0 < a F (n + 1) := by
  ---- Proceed by strong induction on `n`.
  induction' n using Nat.strong_induction_on with n n_ih
  ---- The base case `n = 0` is obvious.
  obtain rfl | hn : n = 0 ∨ 0 < n := n.eq_zero_or_pos
  · rw [a_one, inv_pos]; exact two_pos
  ---- Let `b_i = a_i ((n + 1)/(n + 1 - i) - (n + 2)/(n + 2 - i)` for all `i ≤ n`.
  let b (i) := a F i * ((n + 1 : ℕ) / (n + 1 - i : ℕ) - (n + 2 : ℕ) / ((n + 2 - i) : ℕ))
  ---- By main formula, it suffices to show that `∑_i b_i > 0`.
  suffices 0 < ∑ i ∈ range (n + 1), b i from
    pos_of_mul_pos_right (this.trans_eq (main_formula hn).symm) (n + 2).cast_nonneg
  ---- First, show that `b_0 = 0`.
  have h : b 0 = 0 := by
    have X (k : ℕ) : (k.succ : F) / ((k + 1 - 0 : ℕ) : F) = 1 :=
      div_self (Nat.cast_ne_zero.mpr k.succ_ne_zero)
    dsimp only [b]; rw [X, X, sub_self, mul_zero]
  ---- Second, show that `b_{i + 1} > 0` for any `i < n` (replace the induction hypothesis).
  replace n_ih {i} (hi : i < n) : 0 < b (i +1 ) :=
    mul_pos (n_ih i hi) (sub_pos.mpr (coeff_pos i.succ_pos (Nat.succ_lt_succ hi)))
  ---- Finally, prove that `∑_i b_i > 0`.
  rw [sum_range_succ', h, add_zero]
  exact sum_pos (λ i hi ↦ n_ih (mem_range.mp hi)) (nonempty_range_iff.mpr hn.ne.symm)
