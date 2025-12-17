/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Init

/-!
# IMO 2021 N2 (P1)

Let $n ≥ 99$ be an integer.
The non-negative integers are coloured using two colours.
Prove that there exists $a, b ∈ ℕ$ of the same colour such that
  $n ≤ a < b ≤ 2n$ and $a + b$ is a square.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2021SL.pdf).
-/

namespace IMOSL
namespace IMO2021N2

/-- A positive integer `n` is called *good* if for every colouring of the non-negative
  integers with two colours, there exists `a, b ∈ ℕ` of the same colour such that
  `n ≤ a < b ≤ 2n` and `a + b` is a square. -/
def good (n : ℕ) :=
  ∀ x : ℕ → Bool, ∃ a b, n ≤ a ∧ a < b ∧ b ≤ 2 * n ∧ x a = x b ∧ ∃ k, a + b = k ^ 2

/-- If there exists `a, b, c ∈ ℕ` such that `n ≤ a < b < c ≤ 2n` and
  all of `a + b`, `b + c`, and `c + a` is a square, then `n` is good. -/
theorem good_cond1 (h : n ≤ a) (h0 : a < b) (h1 : b < c) (h2 : c ≤ 2 * n)
    (h3 : a + b = k ^ 2) (h4 : a + c = l ^ 2) (h5 : b + c = m ^ 2) :
    good n := by
  ---- We just divide into cases based on which two out of three has the same colour.
  intro x
  rcases Bool.eq_or_eq_not (x a) (x b) with h6 | h6
  · exact ⟨a, b, h, h0, Nat.le_trans (Nat.le_of_lt h1) h2, h6, k, h3⟩
  rcases Bool.eq_or_eq_not (x c) (x b) with h7 | h7
  · exact ⟨b, c, Nat.le_trans h (Nat.le_of_lt h0), h1, h2, h7.symm, m, h5⟩
  · exact ⟨a, c, h, Nat.lt_trans h0 h1, h2, h6.trans h7.symm, l, h4⟩

/-- If `k^2 + 6k + 8 ≤ n ≤ 2k^2 + 4k` for some `k`, then `n` is good.
  This is equivalent to the official solution's formulation of the step,
  as `2k^2 + 4k = 2(k + 2)^2 - 4(k + 2)` and `2(k^2 + 6k + 8) = 2(k + 2)^2 + 4(k + 2)`. -/
theorem good_cond2 (h : n ≤ 2 * k ^ 2 + 4 * k) (h0 : k ^ 2 + 6 * k + 8 ≤ n) : good n := by
  ---- Set `a = 2k^2 + 4k`, `b = 2k^2 + 8k + 9`, and `c = 2(k^2 + 6k + 8)`.
  refine good_cond1 (b := 2 * k ^ 2 + 8 * k + 9) (k := 2 * k + 3)
    (l := 2 * k + 4) (m := 2 * k + 5) h ?_ ?_ (Nat.mul_le_mul_left 2 h0) ?_ ?_ ?_
  ---- Show that `a < b`.
  · calc 2 * k ^ 2 + 4 * k
    _ ≤ 2 * k ^ 2 + 4 * k + 4 * k := Nat.le_add_right _ _
    _ = 2 * k ^ 2 + 8 * k := by rw [Nat.add_assoc, ← Nat.add_mul]
    _ < 2 * k ^ 2 + 8 * k + 9 := Nat.lt_add_of_pos_right (Nat.succ_pos 8)
  ---- Show that `b < c`.
  · calc 2 * k ^ 2 + 8 * k + 9
    _ ≤ 2 * k ^ 2 + 8 * k + 9 + 4 * k := Nat.le_add_right _ _
    _ = 2 * k ^ 2 + 12 * k + 9 := by
      rw [Nat.add_right_comm, Nat.add_assoc _ (8 * k), ← Nat.add_mul]
    _ < 2 * k ^ 2 + 12 * k + 16 := Nat.lt_add_of_pos_right (Nat.succ_pos 6)
    _ = 2 * (k ^ 2 + 6 * k + 8) := by rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc]
  ---- Show that `a + b = (2k + 3)^2`.
  · calc (2 * k ^ 2 + 4 * k) + (2 * k ^ 2 + 8 * k + 9)
    _ = 4 * k ^ 2 + 12 * k + 9 := by
      rw [← Nat.add_assoc, Nat.add_add_add_comm, ← Nat.add_mul, ← Nat.add_mul]
    _ = 4 * k ^ 2 + 6 * k + (6 * k + 9) := by
      rw [← Nat.add_assoc, Nat.add_assoc (4 * _) (6 * k), ← Nat.add_mul]
    _ = 2 * k * (2 * k + 3) + 3 * (2 * k + 3) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_mul_mul_comm,
        Nat.pow_two, Nat.mul_right_comm 2 k, ← Nat.mul_assoc 3]
    _ = (2 * k + 3) ^ 2 := by rw [Nat.pow_two, Nat.add_mul]
  ---- Show that `b + c = (2k + 4)^2`.
  · calc (2 * k ^ 2 + 4 * k) + 2 * (k ^ 2 + 6 * k + 8)
    _ = 4 * k ^ 2 + 16 * k + 16 := by
      rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_assoc,
        Nat.add_add_add_comm, ← Nat.add_mul, ← Nat.add_mul]
    _ = 4 * k ^ 2 + 8 * k + (8 * k + 16) := by
      rw [← Nat.add_assoc, Nat.add_assoc (4 * _) (8 * k), ← Nat.add_mul]
    _ = 2 * k * (2 * k + 4) + 4 * (2 * k + 4) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_mul_mul_comm,
        Nat.pow_two, Nat.mul_right_comm 2 k, ← Nat.mul_assoc 4 2]
    _ = (2 * k + 4) ^ 2 := by rw [Nat.pow_two, Nat.add_mul]
  ---- Show that `c + a = (2k + 5)^2`.
  · calc (2 * k ^ 2 + 8 * k + 9) + 2 * (k ^ 2 + 6 * k + 8)
    _ = 4 * k ^ 2 + 20 * k + 25 := by
      rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_add_add_comm,
        Nat.add_add_add_comm (2 * k ^ 2), ← Nat.add_mul, ← Nat.add_mul]
    _ = 4 * k ^ 2 + 10 * k + (10 * k + 25) := by
      rw [← Nat.add_assoc, Nat.add_assoc (4 * _) (10 * k), ← Nat.add_mul]
    _ = 2 * k * (2 * k + 5) + 5 * (2 * k + 5) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_mul_mul_comm,
        Nat.pow_two, Nat.mul_right_comm 2 k, ← Nat.mul_assoc 5]
    _ = (2 * k + 5) ^ 2 := by rw [Nat.pow_two, Nat.add_mul]

/-- If `n ≥ 99`, then `k^2 + 6k + 8 ≤ n ≤ 2k^2 + 4k` for some `k`. -/
theorem good_cond2_of_ge99 {n} (hn : n ≥ 99) :
    ∃ k, n ≤ 2 * k ^ 2 + 4 * k ∧ k ^ 2 + 6 * k + 8 ≤ n := by
  ---- Induction on `n`, discharging the base case immediately.
  induction n, hn using Nat.le_induction with
  | base => exact ⟨7, Nat.le_add_left 99 27, Nat.le_refl 99⟩
  | succ n hn hn0 => ?_
  ---- Now suppose `k^2 + 6k + 8 ≤ n ≤ 2k^2 + 4k` for some `k`.
  rcases hn0 with ⟨k, hnk, hnk0⟩
  ---- If `n < 2k^2 + 4k`, we are done.
  obtain hnk | rfl : n < 2 * k ^ 2 + 4 * k ∨ n = 2 * k ^ 2 + 4 * k :=
    (Nat.eq_or_lt_of_le hnk).symm
  · exact ⟨k, hnk, Nat.le_succ_of_le hnk0⟩
  ---- If `n = 2k^2 + 4k`, replace `k` with `k + 1`.
  refine ⟨k + 1, ?_, ?_⟩
  ---- First show that `2k^2 + 4k + 1 ≤ 2(k + 1)^2 + 4(k + 1)`.
  · exact Nat.add_lt_add_of_le_of_lt
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ k) 2))
      (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self k) (Nat.succ_pos 3))
  ---- Now show that `(k + 1)^2 + 6(k + 1) + 8 ≤ 2k^2 + 4k + 1`.
  · clear hnk hnk0
    replace hn : k ≥ 7 := by
      refine Nat.lt_of_not_ge λ (h : k ≤ 6) ↦ Nat.not_lt_of_le hn ?_
      calc 2 * k ^ 2 + 4 * k
        _ ≤ 2 * 6 ^ 2 + 4 * 6 :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h 2))
            (Nat.mul_le_mul_left 4 h)
        _ < 99 := by decide
    calc (k + 1) ^ 2 + 6 * (k + 1) + 8
      _ ≤ (k + 1) ^ 2 + 6 * (k + 1) + (k + 1) := Nat.add_le_add_left (Nat.succ_le_succ hn) _
      _ = (k + 1) ^ 2 + 7 * (k + 1) := by rw [Nat.add_assoc, ← Nat.succ_mul]
      _ ≤ (k + 1) ^ 2 + k * (k + 1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _
      _ = (2 * k + 1) * (k + 1) := by
        rw [Nat.pow_two, ← Nat.add_mul, Nat.two_mul, Nat.add_right_comm]
      _ = 2 * k ^ 2 + 3 * k + 1 := by
        rw [Nat.succ_mul, Nat.mul_succ, Nat.mul_assoc, Nat.pow_two,
          Nat.add_assoc, ← Nat.add_assoc _ k, ← Nat.succ_mul, Nat.add_assoc]
      _ ≤ 2 * k ^ 2 + 4 * k + 1 :=
        Nat.succ_le_succ (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ 3)) _)

/-- Final solution -/
theorem final_solution (hn : n ≥ 99) : good n :=
  (good_cond2_of_ge99 hn).elim λ _ h ↦ good_cond2 h.1 h.2
