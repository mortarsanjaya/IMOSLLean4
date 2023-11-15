/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Tactic.Ring

/-! # IMO 2021 N2 (P1) -/

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
  refine good_cond1 (b := 2 * k ^ 2 + 8 * k + 9) (k := 2 * k + 3) (l := 2 * k + 4)
    (m := 2 * k + 5) h ?_ ?_ (Nat.mul_le_mul_left 2 h0) ?_ ?_ ?_
  -- `2k^2 + 4k < 2k^2 + 8k + 9`
  · rw [Nat.lt_succ_iff, le_iff_exists_add]
    exact ⟨4 * k + 8, by ring⟩
  -- `2k^2 + 8k + 9 < 2(k^2 + 6k + 8)`
  · rw [← Nat.succ_le_iff, Nat.succ_eq_add_one, le_iff_exists_add]
    exact ⟨4 * k + 6, by ring⟩
  -- The three equalities
  all_goals ring

/-- Final solution -/
theorem final_solution (h : 99 ≤ n) : good n := by
  suffices ∃ k, n ≤ 2 * k ^ 2 + 4 * k ∧ k ^ 2 + 6 * k + 8 ≤ n
    from this.elim λ k h0 ↦ good_cond2 h0.1 h0.2
  revert h; refine Nat.le_induction ?_ ?_ n
  -- Base case
  · exact ⟨7, Nat.add_le_add_left (Nat.succ_pos 27) 98, Nat.le_refl 99⟩
  -- Induction step
  · rintro n h ⟨k, h0, h1⟩
    rw [le_iff_lt_or_eq] at h0
    rcases h0 with h0 | rfl
    · exact ⟨k, h0, h1.trans n.le_succ⟩
    · refine ⟨k + 1, le_iff_exists_add.mpr ⟨4 * k + 5, by ring⟩, ?_⟩
      replace h1 : (k + 1) ^ 2 + 6 * (k + 1) + 8
        = 4 * k + 14 + (k ^ 2 + 4 * k + 1) := by ring
      rw [two_mul, (k ^ 2).add_assoc, (k ^ 2).add_assoc, h1, add_le_add_iff_right]
      -- Remaining goal: `4k + 14 ≤ k^2`
      rw [← add_le_add_iff_right 2, mul_assoc 2 2 k, ← mul_add, ← mul_add_one] at h
      replace h : 2 * 7 ^ 2 < 2 * (k ^ 2 + 2 * k + 1) :=
        h.trans' <| le_iff_exists_add.mpr ⟨2, rfl⟩
      rw [← one_pow 2, ← (2 * k).mul_one, ← add_sq] at h
      replace h1 := lt_of_pow_lt_pow' 2 (lt_of_mul_lt_mul_left h (Nat.zero_le 2))
      rw [Nat.lt_succ_iff] at h1
      -- Now we obtained `k ≥ 7`; use it to finish
      apply (add_le_add_left (Nat.mul_le_mul_left 2 h1) _).trans
      rw [sq, ← add_mul]
      exact Nat.mul_le_mul_right k (h1.trans' <| Nat.le_succ 6)
