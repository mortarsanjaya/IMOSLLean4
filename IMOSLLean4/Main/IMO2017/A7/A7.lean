/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs

/-!
# IMO 2017 A7

Let $(b_n)_{n ≥ 0}$ be a sequence of positive integers.
Let $(a_n)_{n ≥ 0}$ be a sequence of integers defined by $a_0 = 0$, $a_1 = 1$, and
* $a_{n + 2} = a_{n + 1} b_{n + 1} + a_n$ if $b_n = 1$;
* $a_{n + 2} = a_{n + 1} b_{n + 1} - a_n$ if $b_n > 1$.

Prove that $\max\{a_n, a_{n + 1}\} ≥ n$ for any $n ≥ 0$.
-/

namespace IMOSL
namespace IMO2017A7

def a (b : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => a b (n + 1) * b (n + 1) + a b n * ite (b n = 1) 1 (-1)

open Finset

variable {b : ℕ → ℤ} (b_pos : ∀ n : ℕ, 0 < b n)
include b_pos

theorem main_equality :
    ∀ n, a b n.succ = (a b n * (b n - 1) + (range n).sum λ i ↦ a b i * |b i - 2|) + 1
  | 0 => by rw [a, a, Int.zero_mul, zero_add, sum_range_zero, zero_add]
  | n + 1 => by
      rw [a, Int.mul_sub, Int.mul_one, ← add_sub_right_comm, add_sub_assoc,
        add_assoc, add_right_inj, main_equality, sum_range_succ_comm,
        ← sub_sub, add_sub_add_right_eq_sub, sub_add_cancel, ← Int.mul_sub]
      specialize b_pos n; rw [← Int.add_one_le_iff, zero_add, le_iff_eq_or_lt] at b_pos
      rcases b_pos with h | h
      · rw [if_pos h.symm, ← h]; rfl
      · have h0 : 0 ≤ b n - 2 := sub_nonneg_of_le (Int.add_one_le_of_lt h)
        rw [if_neg h.ne.symm, abs_of_nonneg h0, sub_sub_sub_cancel_left]; rfl

theorem a_and_sum_nonneg : ∀ n, 0 ≤ a b n ∧ 0 ≤ (range n).sum λ i ↦ a b i * |b i - 2|
  | 0 => ⟨le_refl 0, le_refl 0⟩
  | n + 1 => by
      obtain ⟨h, h0⟩ := a_and_sum_nonneg n
      rw [main_equality b_pos, sum_range_succ]; constructor
      · have h1 : 0 ≤ b n - 1 := by rw [le_sub_iff_add_le, Int.add_one_le_iff]; exact b_pos n
        exact add_nonneg (add_nonneg (Int.mul_nonneg h h1) h0) Int.one_nonneg
      · exact add_nonneg h0 (Int.mul_nonneg h (abs_nonneg _))

theorem a_plus_sum_ge : ∀ n : ℕ, (n : ℤ) ≤ a b n + (range n).sum λ i ↦ a b i * |b i - 2|
  | 0 => le_refl 0
  | n + 1 => by
    apply (add_le_add_right (a_plus_sum_ge n) 1).trans
    rw [sum_range_succ_comm, ← add_assoc, add_right_comm,
      add_le_add_iff_right, main_equality b_pos n, add_right_comm,
      add_le_add_iff_right, add_right_comm, ← Int.mul_add]
    obtain ⟨h, h0⟩ := a_and_sum_nonneg b_pos n
    refine le_add_of_le_of_nonneg ?_ h0
    rw [← add_sub_right_comm, Int.mul_sub, Int.mul_one,
      le_sub_iff_add_le, ← Int.two_mul, Int.mul_comm]
    refine Int.mul_le_mul_of_nonneg_left ?_ h
    rw [← sub_le_iff_le_add', ← neg_sub]; exact neg_le_abs (b n - 2)



/-- Final solution -/
theorem final_solution : ∀ n : ℕ, (n : ℤ) ≤ a b n ∨ (n : ℤ) ≤ a b n.succ
  | 0 => Or.inl (le_refl 0)
  | n + 1 => by
      have h0 (n) : 0 ≤ a b n := (a_and_sum_nonneg b_pos n).1
      refine (Int.add_one_le_of_lt (b_pos n)).lt_or_eq.imp (λ h ↦ ?_) (λ h ↦ ?_)
      ---- Case 1: `b_n > 1`
      · rw [main_equality b_pos, Int.natCast_succ, add_le_add_iff_right]
        refine (a_plus_sum_ge b_pos n).trans (add_le_add_right ?_ _)
        rw [Int.mul_sub, Int.mul_one, le_sub_iff_add_le, ← Int.two_mul, Int.mul_comm]
        exact Int.mul_le_mul_of_nonneg_left h (h0 n)
      ---- Case 2: `b_n = 1`
      · rw [Int.natCast_succ, main_equality b_pos, add_le_add_iff_right]
        apply le_add_of_nonneg_of_le (Int.mul_nonneg (h0 _) (Int.le_sub_one_of_lt (b_pos _)))
        apply (a_plus_sum_ge b_pos n).trans_eq
        rw [sum_range_succ_comm, add_left_inj, ← h]
        exact (mul_one _).symm
