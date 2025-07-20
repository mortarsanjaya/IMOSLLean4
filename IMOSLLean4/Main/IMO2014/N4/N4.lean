/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.NumberTheory.Basic

/-!
# IMO 2014 N4

Prove that, for any positive integer $n > 1$, there exists infinitely many
  positive integers $k$ such that $⌊n^k/k⌋$ is odd.
-/

namespace IMOSL
namespace IMO2014N4

lemma case_odd (hn : 1 < n) (h : Odd n) (k) : Odd (n ^ (n ^ k) / n ^ k) := by
  rw [Nat.pow_div (Nat.lt_pow_self hn).le (Nat.one_pos.trans hn)]; exact h.pow

lemma case_odd_succ (hn : 1 < n) (h : Odd n) (k : ℕ) :
    Odd ((n + 1) ^ (n ^ k.succ) / n ^ k.succ) := by
  have hn' : 0 < n := Nat.one_pos.trans hn
  obtain ⟨C, h0⟩ : ∃ C, n.succ ^ n ^ k.succ = n ^ k.succ * C + 1 := by
    obtain ⟨C, h0⟩ : (n : ℤ) ^ k.succ ∣ n.succ ^ n ^ k.succ - 1 := by
      apply (pow_dvd_pow _ k.succ.le_succ).trans
      rw [← one_pow (n ^ k.succ)]; apply dvd_sub_pow_of_dvd_sub
      rw [Nat.cast_succ, add_sub_cancel_right]
    have h1 : 0 ≤ C := by
      rw [← mul_nonneg_iff_of_pos_left (pow_pos (Nat.cast_pos.mpr hn') k.succ), ← h0]
      exact Int.le_sub_one_of_lt (pow_pos (Nat.cast_pos.mpr n.succ_pos) _)
    lift C to ℕ using h1
    rw [sub_eq_iff_eq_add, ← Nat.cast_pow, ← Nat.cast_pow,
      ← Nat.cast_mul, ← Nat.cast_succ, Nat.cast_inj] at h0
    exact ⟨C, h0⟩
  have h1 : Even (n.succ ^ n ^ k.succ) := by
    refine Nat.even_pow.mpr ⟨?_, pow_ne_zero k.succ hn'.ne.symm⟩
    rwa [Nat.succ_eq_add_one, Nat.even_add_one, Nat.not_even_iff_odd]
  rw [h0, Nat.even_add_one, Nat.not_even_iff_odd, Nat.odd_mul] at h1
  rw [h0, Nat.mul_add_div (Nat.pow_pos hn'),
    Nat.div_eq_of_lt (Nat.one_lt_pow k.succ_ne_zero hn), add_zero]
  exact h1.2

lemma case_two (k : ℕ) : Odd (2 ^ (2 ^ (2 * k.succ) * 3) / (2 ^ (2 * k.succ) * 3)) := by
  have X : 0 < 2 := Nat.succ_pos 1
  have h : 2 * k.succ < 2 ^ (2 * k.succ) * 3 :=
    Nat.lt_two_pow_self.trans_le (Nat.le_mul_of_pos_right _ (Nat.succ_pos 2))
  rw [← Nat.div_div_eq_div_mul, Nat.pow_div h.le X]
  have h0 : 2 ^ (2 * k.succ) = 2 * (2 ^ (2 * k + 1)) := by
    rw [Nat.mul_succ, Nat.pow_succ']
  rw [← Nat.sub_pos_iff_lt, h0, mul_assoc,
    ← Nat.mul_sub, Nat.mul_pos_iff_of_pos_left X] at h
  rw [h0, mul_assoc, ← Nat.mul_sub, Nat.pow_mul]
  generalize 2 ^ (2 * k + 1) * 3 - k.succ = n at h ⊢
  ---- Now prove more generally that `⌊4^n/3⌋` is odd for all `n > 0`
  replace h0 : 4 ^ n = 3 * (4 ^ n / 3) + 4 ^ n % 3 := (Nat.div_add_mod (4 ^ n) 3).symm
  rw [Nat.pow_mod, Nat.one_pow, Nat.one_mod] at h0
  replace h : Even (4 ^ n) := (Nat.even_pow' h.ne.symm).mpr ⟨2, rfl⟩
  rw [h0, Nat.even_add_one, Nat.not_even_iff_odd, Nat.odd_mul] at h
  exact h.2

/-- Final solution -/
theorem final_solution (hn : 1 < n) (N) : ∃ k > N, Odd (n ^ k / k) := by
  obtain rfl | h : n = 2 ∨ 2 < n := LE.le.eq_or_lt' hn
  ---- Case 1: `n` odd
  · refine ⟨2 ^ (2 * N.succ) * 3, ?_, case_two N⟩
    apply (Nat.le_mul_of_pos_right _ (Nat.succ_pos 2)).trans_lt'
    apply Nat.lt_two_pow_self.trans'
    apply (Nat.le_mul_of_pos_left _ (Nat.succ_pos 1)).trans_lt'
    exact N.lt_succ_self
  obtain h0 | h0 : Odd n ∨ Even n := n.even_or_odd.symm
  ---- Case 2: `n = 2`
  · exact ⟨n ^ N, Nat.lt_pow_self hn, case_odd hn h0 N⟩
  ---- Case 3: `n` even
  · obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.one_pos.trans hn).ne.symm
    apply Nat.succ_lt_succ_iff.mp at h
    rw [Nat.even_add_one, Nat.not_even_iff_odd] at h0
    refine ⟨n ^ N.succ, ?_, case_odd_succ h h0 _⟩
    exact N.lt_succ_self.trans (Nat.lt_pow_self h)
