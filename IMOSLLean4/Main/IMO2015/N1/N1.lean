/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Int.Order.Lemmas

/-!
# IMO 2015 N1

Define the function $f : ℤ → ℤ$ by $f(n) = n ⌊n/2⌋$.
Find all integers $M$ such that $f^k(M)$ is even for some $k ∈ ℕ$.

### Notes

The original formulation is slightly different.
Instead of $f : ℤ → ℤ$, we define $f : ℚ → ℚ$ by $f(q) = q ⌊q⌋$.
Then the problem asks for which $M ∈ ℕ^+$ does there exists
  $k ∈ ℕ$ such that $f^k(M + 1/2)$ is an integer.
-/

namespace IMOSL
namespace IMO2015N1

abbrev f (n : ℤ) := n * (n / 2)

theorem main_claim (h : 2 * c ∣ m - 3) (h0 : 2 * c ∣ f m - 3) :
    2 * (2 * c) ∣ m - 3 := by
  rcases eq_or_ne c 0 with rfl | h1
  · exact h
  · rcases h with ⟨d, h⟩
    rw [h, Int.mul_comm]
    apply mul_dvd_mul_left
    have X : (2 : ℤ) ≠ 0 := ne_of_beq_false rfl
    have X0 : (3 / 2 : ℤ) = 1 := rfl
    rw [f, eq_add_of_sub_eq h, add_mul, add_sub_assoc, mul_assoc, ← mul_sub_one,
      dvd_add_right ⟨_, rfl⟩, mul_assoc, add_comm, Int.add_mul_ediv_left _ _ X,
      X0, add_sub_cancel_left, ← two_add_one_eq_three, add_one_mul,
      ← mul_assoc, dvd_add_right ⟨_, rfl⟩, mul_comm] at h0
    exact Int.dvd_of_mul_dvd_mul_left h1 h0

/-- Final solution -/
theorem final_solution : (∃ k : ℕ, 2 ∣ f^[k] M) ↔ M ≠ 3 := by
  rw [iff_not_comm, not_exists]
  refine ⟨λ h n ↦ ?_, λ h ↦ ?_⟩
  ---- `f(3) = 3`, so `2 ∤ f^[n] 3` for any `n : ℕ`
  · have h0 : f 3 = 3 := rfl
    rw [h, Function.iterate_fixed h0]
    exact Int.two_not_dvd_two_mul_add_one 1
  ---- If `2^(n + 1) ∣ f^[k] M - 3` for any `k n : ℕ`, then `M = 3`
  suffices h0 : ∀ n k, 2 ^ (n + 1) ∣ f^[k] M - 3 by
    let K := (M - 3).natAbs
    refine Int.eq_of_sub_eq_zero (Int.eq_zero_of_abs_lt_dvd (h0 K 0) ?_)
    rw [← Int.natCast_natAbs, ← Nat.cast_ofNat (n := 2), ← Int.natCast_pow]
    exact Int.ofNat_lt.mpr (K.lt_succ_self.trans K.succ.lt_two_pow_self)
  ---- For any `k n : ℕ`, we have `2^(n + 1) ∣ f^[k] M - 3`
  refine Nat.rec (λ k ↦ ?_) (λ n h0 k ↦ ?_)
  · rw [Int.dvd_iff_emod_eq_zero, Nat.zero_add, pow_one,
      ← Int.even_iff, Int.even_sub', ← Int.not_even_iff_odd,
      Int.even_iff, ← Int.dvd_iff_emod_eq_zero]
    exact iff_of_true (h k) (Int.odd_iff.mpr rfl)
  · rw [pow_succ', pow_succ']
    refine main_claim ?_ ?_
    · rw [← pow_succ']; exact h0 k
    · rw [← pow_succ', ← f.iterate_succ_apply']; exact h0 (k + 1)
