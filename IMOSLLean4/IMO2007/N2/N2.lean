/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int

/-!
# IMO 2007 N2

Fix integers $b > 0$ and $n ≥ 0$.
Suppose that for each $k ∈ ℕ^+$, there exists an integer $a$ such that $k ∣ b - a^n$.
Prove that $b = A^n$ for some integer $A$.
-/

namespace IMOSL
namespace IMO2007N2

/-- Final solution with explicit `k` -/
theorem final_solution_explicit (h : 0 < b) (h0 : ∃ c : ℤ, (b ^ 2 : ℤ) ∣ b - c ^ n) :
    ∃ a : ℤ, b = a ^ n := by
  obtain ⟨c, h1⟩ : ∃ c, Associated (c ^ n) b := by
    rcases h0 with ⟨c, a, h0⟩
    rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', sq, mul_assoc, ← mul_one_sub] at h0
    have h1 : gcd b (1 - b * a) = 1 := by
      have h1 : b ∣ (1 - b * a) - 1 := ⟨-a, by rw [sub_sub_cancel_left, mul_neg]⟩
      exact (gcd_eq_of_dvd_sub_right h1).trans (gcd_one_right b)
    exact exists_associated_pow_of_mul_eq_pow (Int.isUnit_iff.mpr (Or.inl h1)) h0
  rw [Int.associated_iff, eq_neg_iff_add_eq_zero, add_comm, ← eq_neg_iff_add_eq_zero] at h1
  rcases h1 with rfl | rfl
  · exact ⟨c, rfl⟩
  · refine ⟨-c, ((Nat.not_even_iff_odd.mp λ h1 ↦ h.not_le ?_).neg_pow c).symm⟩
    exact Int.neg_nonpos_of_nonneg (h1.pow_nonneg c)

/-- Final solution -/
theorem final_solution (h : 0 < b) (h0 : ∀ k : ℕ, 0 < k → ∃ c : ℤ, (k : ℤ) ∣ b - c ^ n) :
    ∃ a : ℤ, b = a ^ n := by
  lift b to ℕ using h.le
  exact final_solution_explicit h (h0 (b ^ 2) (Nat.pow_pos (Int.ofNat_pos.mp h)))
