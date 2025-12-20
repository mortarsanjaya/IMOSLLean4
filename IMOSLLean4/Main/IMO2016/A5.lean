/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Parity

/-!
# IMO 2016 A5

1. Prove that, for every $n ∈ ℕ$, there exists some $a, b ∈ ℕ$
  such that $0 < b ≤ \sqrt{n} + 1$ and $b^2 n ≤ a^2 ≤ b^2 (n + 1)$.
2. Prove that, for infinitely many $n ∈ ℕ$, there does not exist $a, b ∈ ℕ$
  such that $0 < b ≤ \sqrt{n}$ and $b^2 n ≤ a^2 ≤ b^2 (n + 1)$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2016SL.pdf).
Note that for part 1, we also include the case $n = 0$.
-/

namespace IMOSL
namespace IMO2016A5

/-- Final solution, part 1 -/
theorem final_solution_part1 (n) :
    ∃ a, ∃ b > 0, b ≤ Nat.sqrt n + 1 ∧ b ^ 2 * n ≤ a ^ 2 ∧ a ^ 2 ≤ b ^ 2 * (n + 1) := by
  ---- If `n = 0`, choose `a = 0` and `b = 1`.
  obtain rfl | hn : n = 0 ∨ n > 0 := Nat.eq_zero_or_pos n
  · exact ⟨0, 1, Nat.one_pos, Nat.le_refl 1, Nat.le_refl 0, Nat.zero_le _⟩
  ---- Now write `n = r^2 + s`, where `r > 0` and `s ≤ 2r`.
  obtain ⟨r, hr, s, hs, rfl⟩ : ∃ r > 0, ∃ s ≤ r + r, r ^ 2 + s = n := by
    refine ⟨Nat.sqrt n, Nat.sqrt_pos.mpr hn, n - Nat.sqrt n ^ 2,
      Nat.sub_le_of_le_add ?_, Nat.add_sub_of_le (Nat.sqrt_le' n)⟩
    rw [Nat.pow_two, Nat.add_comm, ← Nat.add_assoc]
    exact Nat.sqrt_le_add n
  ---- Divide into cases based on the parity of `s`.
  clear hn; rw [Nat.sqrt_add_eq' r hs]
  obtain ⟨k, rfl | rfl⟩ : ∃ k, s = 2 * k ∨ s = 2 * k + 1 := Nat.even_or_odd' s
  ---- If `s = 2k` is even, then pick `a = r^2 + k` and `b = r`.
  · replace hs : k ≤ r := by rwa [← Nat.two_mul, Nat.mul_le_mul_left_iff Nat.two_pos] at hs
    refine ⟨r ^ 2 + k, r, hr, Nat.le_succ r, ?_⟩
    rw [Nat.mul_succ, Nat.mul_add, ← Nat.pow_two, Nat.mul_left_comm, ← Nat.mul_assoc, add_sq]
    exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.pow_le_pow_left hs 2) _⟩
  ---- If `s = 2k + 1` is odd, then pick `a = r^2 + r + k + 1` and `b = r + 1`.
  · replace hs : k ≤ r := by
      rw [Nat.succ_le_iff, ← Nat.two_mul, Nat.mul_lt_mul_left Nat.two_pos] at hs
      exact Nat.le_of_lt hs
    refine ⟨r ^ 2 + (2 * k + 1) + (r - k), r + 1, Nat.succ_pos r, Nat.le_refl _, ?_⟩
    replace hr : (r ^ 2 + (2 * k + 1) + (r - k)) ^ 2
        = (r + 1) ^ 2 * (r ^ 2 + (2 * k + 1)) + (r - k) ^ 2 := by
      rw [add_sq, Nat.add_left_inj, Nat.pow_two, Nat.mul_right_comm, ← Nat.add_mul]
      refine congrArg (· * _) ?_
      rw [Nat.add_assoc, Nat.add_right_comm, ← Nat.mul_add, Nat.add_sub_cancel' hs,
        add_sq, Nat.mul_one, Nat.one_pow, Nat.add_assoc]
    replace hs : r - k ≤ r + 1 := Nat.le_of_lt (Nat.sub_lt_succ r k)
    exact hr ▸ ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.pow_le_pow_left hs 2) _⟩

/-- Final solution, part 2, explicit version -/
theorem final_solution_part2_explicit (k) :
    ¬∃ a, ∃ b > 0, b ≤ k ∧ b ^ 2 * (k ^ 2 + 1) ≤ a ^ 2 ∧ a ^ 2 ≤ b ^ 2 * (k ^ 2 + 2) := by
  ---- If there is such `a` and `b`, then `(bk)^2 < a^2 < (bk + 1)^2`.
  rintro ⟨a, b, h, h0, h1, h2⟩
  refine Nat.not_exists_sq (m := b * k) (n := a ^ 2) ?_ ?_ ⟨a, (Nat.pow_two a).symm⟩
  ---- Prove the claim `(bk)^2 < a^2`.
  · calc (b * k) * (b * k)
      _ = b ^ 2 * k ^ 2 := by rw [← Nat.pow_two, Nat.mul_pow]
      _ < b ^ 2 * (k ^ 2 + 1) := Nat.lt_add_of_pos_right (Nat.pow_pos h)
      _ ≤ a ^ 2 := h1
  ---- Prove the claim `a^2 < (bk + 1)^2`.
  · replace h0 : b * b ≤ b * k := Nat.mul_le_mul_left b h0
    calc a ^ 2
      _ ≤ b ^ 2 * k ^ 2 + b ^ 2 + b ^ 2 := h2
      _ = (b * k) * (b * k) + b * b + b * b := by
        rw [Nat.pow_two, Nat.pow_two, Nat.mul_mul_mul_comm]
      _ ≤ (b * k) * (b * k) + b * k + b * k :=
        Nat.add_le_add (Nat.add_le_add_left h0 _) h0
      _ < (b * k) * (b * k) + b * k + b * k + 1 := Nat.lt_succ_self _
      _ = (b * k + 1) * (b * k + 1) := by
        rw [Nat.succ_mul, Nat.mul_succ, Nat.add_assoc]

/-- Final solution, part 2 -/
theorem final_solution_part2 (N) :
    ∃ n > N, ¬∃ a, ∃ b > 0, b ≤ Nat.sqrt n ∧
      b ^ 2 * n ≤ a ^ 2 ∧ a ^ 2 ≤ b ^ 2 * (n + 1) := by
  ---- Pick `n = (N + 1)^2 + 1` and verify everything.
  refine ⟨(N + 1) * (N + 1) + 1, ?_, ?_⟩
  · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le N.lt_succ_self N.succ.le_mul_self)
  · rw [Nat.sqrt_add_eq N.succ (Nat.le_add_left 1 _), ← Nat.pow_two]
    exact final_solution_part2_explicit N.succ
