/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
# IMO 2012 N3

Determine all integers $m > 1$ such that $n ∣ \binom{n}{m - 2n}$ for every $n ≤ m/2$.
-/

namespace IMOSL
namespace IMO2012N3

theorem prime_not_dvd_descFactorial (h : p.Prime) (k : ℕ) :
    ∀ r < p, ¬p ∣ (p * k + r).descFactorial r := by
  refine Nat.rec (λ _ ↦ h.not_dvd_one) (λ r h0 h1 ↦ ?_)
  rw [Nat.add_succ, Nat.succ_descFactorial_succ]
  refine h.not_dvd_mul ?_ (h0 <| r.lt_succ_self.trans h1)
  rw [add_assoc, Nat.dvd_add_right ⟨k, rfl⟩]
  exact Nat.not_dvd_of_pos_of_lt r.succ_pos h1

theorem prime_binom_not_dvd (h : p.Prime) (h0 : k ≠ 0) :
    ¬(p * k) ∣ (p * k).choose p := λ h1 ↦ by
  apply prime_not_dvd_descFactorial h k.pred p.pred (p.pred_lt_self h.pos)
  rw [← Nat.mul_dvd_mul_iff_left (p * k.pred + p.pred).succ_pos,
    ← Nat.succ_descFactorial_succ, ← Nat.succ_eq_add_one, ← Nat.add_succ,
    ← Nat.succ_eq_add_one, Nat.succ_pred h.ne_zero, ← p.mul_succ,
    Nat.succ_pred h0, Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
  exact mul_dvd_mul (Nat.dvd_factorial h.pos p.le_refl) h1

/-- Final solution -/
theorem final_solution (h : 1 < m) :
    (∀ n : ℕ, 2 * n ≤ m → n ∣ n.choose (m - 2 * n)) ↔ m.Prime := by
  refine ⟨λ h0 ↦ ?_, λ h0 n h1 ↦ ?_⟩
  by_cases h1 : 2 ∣ m
  ---- If `m` is even and "good", then `m = 2`
  · rcases h1 with ⟨k, rfl⟩
    specialize h0 k (2 * k).le_refl
    rw [Nat.sub_self, k.choose_zero_right, Nat.dvd_one] at h0
    rw [h0]; exact Nat.prime_two
  ---- If `m` is odd and composite, then `m` is not "good"
  · obtain ⟨p, h2, k, rfl⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ m :=
      ⟨m.minFac, Nat.minFac_prime h.ne.symm, m.minFac_dvd⟩
    rw [Nat.two_dvd_ne_zero, ← Nat.odd_iff, Nat.odd_mul] at h1
    rcases h1 with ⟨-, k, rfl⟩
    suffices k = 0 by rwa [this, mul_zero, zero_add, mul_one]
    by_contra h1; apply prime_binom_not_dvd h2 h1
    specialize h0 (p * k)
    rw [Nat.mul_add_one, Nat.mul_left_comm, Nat.add_sub_cancel_left] at h0
    exact h0 (Nat.le_add_right (p * (2 * k)) p)
  ---- If `m` is prime, then `m` is "good"
  · rcases Nat.exists_eq_add_of_le h1 with ⟨c, rfl⟩
    rw [Nat.add_sub_cancel_left]; rcases c with _ | c
    -- `c = 0`
    · rw [Nat.add_zero, Nat.prime_mul_iff] at h0
      rcases h0 with ⟨-, rfl⟩ | ⟨-, h1⟩
      exacts [Nat.dvd_refl 1, absurd h1 (Nat.succ_ne_self 1)]
    rcases n with _ | n
    -- `n = 0`
    · exact Nat.dvd_refl 0
    -- `c, n > 0`
    · refine (Nat.Coprime.dvd_mul_right ?_).mp ⟨_, (n.succ_mul_choose_eq c).symm⟩
      rw [Nat.two_mul, Nat.add_assoc] at h0
      rw [← Nat.coprime_self_add_right, ← Nat.coprime_self_add_right,
        Nat.coprime_comm, h0.coprime_iff_not_dvd]
      exact Nat.not_dvd_of_pos_of_lt n.succ_pos (Nat.lt_add_of_pos_right (n.succ + c).succ_pos)
