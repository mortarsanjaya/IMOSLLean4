/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Basic

/-!
# IMO 2016 A5

1. Prove that, for every $n ∈ ℕ$, there exists some $a, b ∈ ℕ$
  such that $0 < b ≤ \sqrt{n} + 1$ and $b^2 n ≤ a^2 ≤ b^2 (n + 1)$.
2. Prove that, for infinitely many $n ∈ ℕ$, there does not exist $a, b ∈ ℕ$
  such that $0 < b ≤ \sqrt{n}$ and $b^2 n ≤ a^2 ≤ b^2 (n + 1)$.
-/

namespace IMOSL
namespace IMO2016A5

/-- Final solution, part 1 -/
theorem final_solution_part1 (n) :
    ∃ a b, 0 < b ∧ b ≤ n.sqrt + 1 ∧ b ^ 2 * n ≤ a ^ 2 ∧ a ^ 2 ≤ b ^ 2 * (n + 1) := by
  ---- Start directly with case dividing `s` (`r = 0` dealt later)
  obtain ⟨r, s, h, rfl⟩ : ∃ r s, s ≤ r + r ∧ r ^ 2 + s = n := by
    refine ⟨n.sqrt, n - n.sqrt ^ 2, Nat.sub_le_of_le_add ?_, Nat.add_sub_of_le n.sqrt_le'⟩
    rw [← add_rotate, sq]; exact n.sqrt_le_add
  rw [Nat.sqrt_add_eq' r h]
  obtain ⟨k, rfl | rfl⟩ : ∃ k, s = 2 * k ∨ s = 2 * k + 1 := s.even_or_odd'
  ---- Case 1: `s` is even
  · replace h : k ≤ r := Nat.le_of_mul_le_mul_left (by rwa [r.two_mul]) Nat.two_pos
    obtain rfl | h0 : r = 0 ∨ 0 < r := r.eq_zero_or_pos
    -- Subcase `r = 0`
    · refine ⟨0, 1, Nat.one_pos, Nat.le_refl 1, ?_, Nat.zero_le _⟩
      rw [Nat.le_zero.mp h]; exact Nat.zero_le 0
    -- Now focus on the subcase `r > 0`
    obtain ⟨a, h1⟩ : ∃ a, a ^ 2 = r ^ 2 * (r ^ 2 + 2 * k) + k ^ 2 :=
      ⟨r ^ 2 + k, by rw [add_sq, sq, mul_assoc, mul_left_comm, ← mul_add]⟩
    refine ⟨a, r, h0, r.le_succ, h1 ▸ ⟨Nat.le_add_right _ _, ?_⟩⟩
    exact Nat.add_le_add_left (Nat.pow_le_pow_left h 2) _
  ---- Case 2: `s` is odd
  · replace h : k < r := by
      rwa [Nat.succ_le_iff, ← Nat.two_mul, Nat.mul_lt_mul_left Nat.two_pos] at h
    obtain ⟨a, h0⟩ : ∃ a, a ^ 2 = (r + 1) ^ 2 * (r ^ 2 + (2 * k + 1)) + (r - k) ^ 2 := by
      refine ⟨r ^ 2 + 1 + k + r, ?_⟩
      rw [add_sq r, mul_one, one_pow, add_right_comm _ (2 * r),
        ← add_assoc, add_right_comm _ (2 * k), add_assoc]
      generalize r ^ 2 + 1 = N
      obtain ⟨m, rfl⟩ : ∃ m, r = k + m := Nat.exists_eq_add_of_le h.le
      rw [Nat.add_sub_cancel_left, ← k.add_assoc, ← two_mul, mul_add 2,
        ← add_assoc, ← add_assoc, add_sq, sq, mul_right_comm, ← add_mul]
    refine ⟨a, r + 1, r.succ_pos, le_refl _, h0 ▸ ⟨Nat.le_add_right _ _, ?_⟩⟩
    exact Nat.add_le_add_left (Nat.pow_le_pow_left (r.sub_lt_succ k).le 2) _

/-- Final solution, part 2, explicit version -/
theorem final_solution_part2_general (k) :
    ¬∃ a b, 0 < b ∧ b ≤ k ∧ b ^ 2 * (k ^ 2 + 1) ≤ a ^ 2 ∧ a ^ 2 ≤ b ^ 2 * (k ^ 2 + 2) := by
  rintro ⟨a, b, h, h0, h1, h2⟩
  replace h1 : (b * k) * (b * k) < a ^ 2 := by
    rw [← sq, mul_pow]; exact (Nat.lt_add_of_pos_right (Nat.pow_pos h)).trans_le h1
  replace h2 : a ^ 2 < (b * k + 1) * (b * k + 1) := by
    rw [← sq, add_sq, mul_pow, mul_one, one_pow, Nat.lt_add_one_iff]
    refine h2.trans ((b ^ 2).mul_add _ _ ▸ Nat.add_le_add_left ?_ _)
    rw [mul_comm, sq]; exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left b h0)
  exact Nat.not_exists_sq h1 h2 ⟨a, (sq a).symm⟩

/-- Final solution, part 2 -/
theorem final_solution_part2 (N) :
    ∃ n > N, ¬∃ a b, 0 < b ∧ b ≤ n.sqrt ∧ b ^ 2 * n ≤ a ^ 2 ∧ a ^ 2 ≤ b ^ 2 * (n + 1) := by
  refine ⟨N.succ * N.succ + 1, ?_, ?_⟩
  · exact Nat.lt_succ_of_lt (N.lt_succ_self.trans_le N.succ.le_mul_self)
  · rw [Nat.sqrt_add_eq N.succ (Nat.le_add_left 1 _), ← sq]
    exact final_solution_part2_general N.succ
