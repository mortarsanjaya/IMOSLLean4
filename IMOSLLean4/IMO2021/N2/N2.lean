/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Algebra.Ring.Nat

/-!
# IMO 2021 N2 (P1)

Let $n ≥ 99$ be an integer.
The non-negative integers are coloured using two colours.
Prove that there exists $a, b ∈ ℕ$ of the same colour such that
  $n ≤ a < b ≤ 2n$ and $a + b$ is a square.
-/

namespace IMOSL
namespace IMO2021N2

def good (n : ℕ) := ∀ x : ℕ → Bool, ∃ a b : ℕ,
  n ≤ a ∧ a < b ∧ b ≤ 2 * n ∧ x a = x b ∧ ∃ k, a + b = k ^ 2

theorem good_cond1 (h : n ≤ a) (h0 : a < b) (h1 : b < c) (h2 : c ≤ 2 * n)
    (h3 : a + b = k ^ 2) (h4 : a + c = l ^ 2) (h5 : b + c = m ^ 2) :
    good n := λ x ↦ by
  rcases (x a).eq_or_eq_not (x b) with h6 | h6
  · exact ⟨a, b, h, h0, h1.le.trans h2, h6, k, h3⟩
  rcases (x c).eq_or_eq_not (x b) with h7 | h7
  · exact ⟨b, c, h.trans h0.le, h1, h2, h7.symm, m, h5⟩
  · exact ⟨a, c, h, h0.trans h1, h2, h6.trans h7.symm, l, h4⟩

theorem good_cond2 (h : n ≤ 2 * k ^ 2 + 4 * k) (h0 : k ^ 2 + 6 * k + 8 ≤ n) :
    good n := by
  refine good_cond1 (b := 2 * k ^ 2 + 8 * k + 9) (k := 2 * k + 3)
    (l := 2 * k + 4) (m := 2 * k + 5) h ?_ ?_
    (Nat.mul_le_mul_left 2 h0) ?_ ?_ ?_
  -- `2k^2 + 4k < 2k^2 + 8k + 9`
  · rw [Nat.add_assoc, Nat.add_lt_add_iff_left, Nat.lt_succ_iff]
    refine (Nat.mul_le_mul_right k ?_).trans (Nat.le_add_right _ _)
    exact Nat.le_mul_of_pos_left 4 (Nat.succ_pos 1)
  -- `2k^2 + 8k + 9 < 2(k^2 + 6k + 8)`
  · rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc,
      Nat.lt_succ_iff, Nat.add_assoc, Nat.add_assoc,
      Nat.add_le_add_iff_left, Nat.add_le_add_iff_right]
    refine (Nat.mul_le_mul_right k ?_).trans (Nat.le_add_right _ _)
    exact Nat.mul_le_mul_left 4 (Nat.le_succ 2)
  -- `2k^2 + 4k + (2k^2 + 8k + 9) = (2k + 3)^2`
  · rw [← Nat.add_assoc, Nat.add_add_add_comm, ← Nat.add_mul, ← Nat.add_mul,
      add_sq, Nat.mul_pow, Nat.mul_right_comm, ← Nat.mul_assoc]
    rfl
  -- `2k^2 + 4k + 2(k^2 + 6k + 8) = (2k + 4)^2`
  · rw [Nat.mul_add, ← Nat.add_assoc, Nat.mul_add, Nat.add_add_add_comm,
      ← Nat.add_mul, ← Nat.mul_assoc, ← Nat.add_mul, add_sq, Nat.mul_pow,
      Nat.mul_right_comm, ← Nat.mul_assoc]
    rfl
  -- `2k^2 + 8k + 9 + 2(k^2 + 6k + 8) = (2k + 5)^2`
  · rw [Nat.mul_add, Nat.add_add_add_comm, Nat.mul_add, ← Nat.mul_assoc,
      Nat.add_add_add_comm (2 * k ^ 2), ← Nat.add_mul, ← Nat.add_mul,
      add_sq, Nat.mul_pow, Nat.mul_right_comm, ← Nat.mul_assoc]
    rfl

theorem good_cond2_k_witness :
    ∀ n, 99 ≤ n → ∃ k, n ≤ 2 * k ^ 2 + 4 * k ∧ k ^ 2 + 6 * k + 8 ≤ n :=
  Nat.le_induction
  ---- Base case
  ⟨7, Nat.add_le_add_left (Nat.succ_pos 27) 98, Nat.le_refl 99⟩
  ---- Induction step
  λ n h h0 ↦ by
    rcases h0 with ⟨k, h0, h1⟩
    rw [le_iff_lt_or_eq] at h0; rcases h0 with h0 | rfl
    · exact ⟨k, h0, Nat.le_succ_of_le h1⟩
    refine ⟨k + 1, ?_, ?_⟩
    ---- `2k^2 + 4k + 1 < 2(k + 1)^2 + 4(k + 1)`
    · rw [Nat.mul_succ, ← Nat.add_assoc]
      exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 <|
        Nat.pow_le_pow_of_le_left k.le_succ 2) _) (Nat.le_add_left 1 3)
    ---- `(k + 1)^2 + 6(k + 1) + 8 ≤ 2k^2 + 4k + 1`
    · replace h1 : 2 * k ^ 2 + 4 * k + 2 = 2 * (k + 1) ^ 2 := by
        rw [add_sq, Nat.mul_add, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc]; rfl
      rw [← Nat.add_le_add_iff_right (n := 2), h1, Nat.succ_le_iff, Nat.mul_comm,
        ← Nat.div_lt_iff_lt_mul (Nat.succ_pos 1), ← Nat.sqrt_lt'] at h
      change 8 ≤ k + 1 at h -- This is a bit slow, but it seems unavoidable
      rw [← Nat.add_le_add_iff_right (n := 1), h1, Nat.two_mul,
        Nat.add_assoc, Nat.add_assoc, Nat.add_le_add_iff_left, sq]
      apply (Nat.mul_le_mul_right _ h).trans'
      rw [Nat.add_mul 6 2, Nat.add_le_add_iff_left, Nat.two_mul]
      exact Nat.add_le_add h (Nat.le_add_left 1 k)



/-- Final solution -/
theorem final_solution (h : 99 ≤ n) : good n :=
  (good_cond2_k_witness n h).elim λ _ h ↦ good_cond2 h.1 h.2
