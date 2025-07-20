/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Tactic.NormNum.NatSqrt

/-!
# IMO 2021 N2 (P1)

Let $n ≥ 99$ be an integer.
The non-negative integers are coloured using two colours.
Prove that there exists $a, b ∈ ℕ$ of the same colour such that
  $n ≤ a < b ≤ 2n$ and $a + b$ is a square.
-/

namespace IMOSL
namespace IMO2021N2

def good (n : ℕ) :=
  ∀ x : ℕ → Bool, ∃ a b, n ≤ a ∧ a < b ∧ b ≤ 2 * n ∧ x a = x b ∧ ∃ k, a + b = k ^ 2

theorem good_cond1 (h : n ≤ a) (h0 : a < b) (h1 : b < c) (h2 : c ≤ 2 * n)
    (h3 : a + b = k ^ 2) (h4 : a + c = l ^ 2) (h5 : b + c = m ^ 2) :
    good n := λ x ↦ by
  /- `X` is essentially `Bool.eq_or_eq_not`, but reimplemented to avoid extra imports -/
  have X : ∀ a b : Bool, a = b ∨ a = !b := by decide
  rcases X (x a) (x b) with h6 | h6
  · exact ⟨a, b, h, h0, Nat.le_trans (Nat.le_of_lt h1) h2, h6, k, h3⟩
  rcases X (x c) (x b) with h7 | h7
  · exact ⟨b, c, Nat.le_trans h (Nat.le_of_lt h0), h1, h2, h7.symm, m, h5⟩
  · exact ⟨a, c, h, Nat.lt_trans h0 h1, h2, h6.trans h7.symm, l, h4⟩

theorem good_cond2 (h : n ≤ 2 * k ^ 2 + 4 * k) (h0 : k ^ 2 + 6 * k + 8 ≤ n) : good n := by
  refine good_cond1 (b := 2 * k ^ 2 + 8 * k + 9) (k := 2 * k + 3)
    (l := 2 * k + 4) (m := 2 * k + 5) h ?_ ?_ (Nat.mul_le_mul_left 2 h0) ?_ ?_ ?_
  -- `2k^2 + 4k < 2k^2 + 8k + 9`
  · calc
    _ ≤ 2 * k ^ 2 + 4 * k + 4 * k := Nat.le_add_right _ _
    _ = 2 * k ^ 2 + 8 * k := by rw [Nat.add_assoc, ← Nat.add_mul]
    _ < 2 * k ^ 2 + 8 * k + 9 := Nat.lt_add_of_pos_right (Nat.succ_pos 8)
  -- `2k^2 + 8k + 9 < 2(k^2 + 6k + 8)`
  · calc
    _ ≤ 2 * k ^ 2 + 8 * k + 9 + 4 * k := Nat.le_add_right _ _
    _ = 2 * k ^ 2 + 12 * k + 9 := by
      rw [Nat.add_right_comm, Nat.add_assoc _ (8 * k), ← Nat.add_mul]
    _ < 2 * k ^ 2 + 12 * k + 16 := Nat.lt_add_of_pos_right (Nat.succ_pos 6)
    _ = 2 * (k ^ 2 + 6 * k + 8) := by rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc]
  -- `2k^2 + 4k + (2k^2 + 8k + 9) = (2k + 3)^2`
  · calc
    _ = 4 * k ^ 2 + 12 * k + 9 := by
      rw [← Nat.add_assoc, Nat.add_add_add_comm, ← Nat.add_mul, ← Nat.add_mul]
    _ = 4 * k ^ 2 + 6 * k + (6 * k + 9) := by
      rw [← Nat.add_assoc, Nat.add_assoc (4 * _) (6 * k), ← Nat.add_mul]
    _ = 2 * k * (2 * k + 3) + 3 * (2 * k + 3) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_mul_mul_comm,
        Nat.pow_two, Nat.mul_right_comm 2 k, ← Nat.mul_assoc 3]
    _ = (2 * k + 3) ^ 2 := by rw [Nat.pow_two, Nat.add_mul]
  -- `2k^2 + 4k + 2(k^2 + 6k + 8) = (2k + 4)^2`
  · calc
    _ = 4 * k ^ 2 + 16 * k + 16 := by
      rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_assoc,
        Nat.add_add_add_comm, ← Nat.add_mul, ← Nat.add_mul]
    _ = 4 * k ^ 2 + 8 * k + (8 * k + 16) := by
      rw [← Nat.add_assoc, Nat.add_assoc (4 * _) (8 * k), ← Nat.add_mul]
    _ = 2 * k * (2 * k + 4) + 4 * (2 * k + 4) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_mul_mul_comm,
        Nat.pow_two, Nat.mul_right_comm 2 k, ← Nat.mul_assoc 4 2]
    _ = (2 * k + 4) ^ 2 := by rw [Nat.pow_two, Nat.add_mul]
  -- `2k^2 + 8k + 9 + 2(k^2 + 6k + 8) = (2k + 5)^2`
  · calc
    _ = 4 * k ^ 2 + 20 * k + 25 := by
      rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_add_add_comm,
        Nat.add_add_add_comm (2 * k ^ 2), ← Nat.add_mul, ← Nat.add_mul]
    _ = 4 * k ^ 2 + 10 * k + (10 * k + 25) := by
      rw [← Nat.add_assoc, Nat.add_assoc (4 * _) (10 * k), ← Nat.add_mul]
    _ = 2 * k * (2 * k + 5) + 5 * (2 * k + 5) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_mul_mul_comm,
        Nat.pow_two, Nat.mul_right_comm 2 k, ← Nat.mul_assoc 5]
    _ = (2 * k + 5) ^ 2 := by rw [Nat.pow_two, Nat.add_mul]

theorem good_cond2_k_witness :
    ∀ n, 99 ≤ n → ∃ k, n ≤ 2 * k ^ 2 + 4 * k ∧ k ^ 2 + 6 * k + 8 ≤ n := by
  ---- Induction on `n`, discharging the base case immediately
  refine Nat.le_induction ⟨7, Nat.le_add_left 99 27, Nat.le_refl 99⟩ λ n h h0 ↦ ?_
  rcases h0 with ⟨k, h0, h1⟩
  rw [le_iff_lt_or_eq] at h0; rcases h0 with h0 | rfl
  · exact ⟨k, h0, Nat.le_succ_of_le h1⟩
  refine ⟨k + 1, ?_, ?_⟩
  ---- `2k^2 + 4k + 1 < 2(k + 1)^2 + 4(k + 1)`
  · rw [Nat.mul_succ, ← Nat.add_assoc]
    refine Nat.add_le_add (Nat.add_le_add_right ?_ _) (Nat.le_add_left 1 3)
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left k.le_succ 2)
    ---- `(k + 1)^2 + 6(k + 1) + 8 ≤ 2k^2 + 4k + 1`
  · replace h1 : 2 * k ^ 2 + 4 * k + 2 = 2 * (k + 1) ^ 2 := calc
      _ = 2 * (k ^ 2 + 2 * k + 1) := by rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc]
      _ = _ := by rw [Nat.pow_two, k.two_mul, ← Nat.add_assoc,
        ← k.mul_succ, Nat.add_assoc, ← k.succ_mul, Nat.pow_two]
    replace h : 8 ≤ k + 1 := by
      have h0 : ((99 + 1) / Nat.succ 1).sqrt = 7 := by norm_num
      rwa [← Nat.add_le_add_iff_right (n := 2), h1, Nat.succ_le_iff, Nat.mul_comm,
        ← Nat.div_lt_iff_lt_mul (Nat.succ_pos 1), ← Nat.sqrt_lt', h0] at h
    apply Nat.le_of_succ_le_succ; calc
      _ = (k + 1) ^ 2 + 6 * k + 15 := rfl
      _ ≤ (k + 1) ^ 2 + 6 * (k + 1) + 2 * (k + 1) := by
        apply Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 6 k.le_succ) _)
        exact Nat.le_of_lt (Nat.mul_le_mul_left 2 h)
      _ = (k + 1) ^ 2 + 8 * (k + 1) := by rw [Nat.add_assoc, ← Nat.add_mul]
      _ ≤ (k + 1) ^ 2 + (k + 1) * (k + 1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
      _ = 2 * k ^ 2 + 4 * k + 2 := by rw [h1, Nat.two_mul, ← Nat.pow_two]



/-- Final solution -/
theorem final_solution (h : 99 ≤ n) : good n :=
  (good_cond2_k_witness n h).elim λ _ h ↦ good_cond2 h.1 h.2
