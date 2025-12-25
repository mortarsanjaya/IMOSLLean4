/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Factorization.Basic

/-!
# IMO 2024 N1

Find all positive integers $n$ such that for any $d ∈ ℕ⁺$ with $d ∣ n$,
  we have either $d + 1 ∣ n$ or that $d + 1$ is prime.

### Answer

$1$, $2$, $4$, and $12$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2024SL.pdf).
-/

namespace IMOSL
namespace IMO2024N1

/-- An integer `n ≥ 0` is called *good* if for any `d ∣ n`,
  it holds that either `d + 1 ∣ n` or `d + 1` is prime. -/
def good (n : ℕ) := ∀ d, d ∣ n → d + 1 ∣ n ∨ Nat.Prime (d + 1)

/-- `9` is not prime. -/
theorem not_prime_nine : ¬Nat.Prime 9 := by
  decide

/-- If `2^k` is good, then `k ≤ 2`. -/
theorem good_two_pow_imp {k} (hk : good (2 ^ k)) : k ≤ 2 := by
  ---- Suppose `k ≥ 3`.
  refine Nat.le_of_not_lt λ hk0 ↦ ?_
  ---- Since `8 ∣ 2^k` and `9` is not prime, we have `9 ∣ 2^k`.
  replace hk : 9 ∣ 2 ^ k := (hk 8 (Nat.pow_dvd_pow 2 hk0)).resolve_right not_prime_nine
  ---- But then `3 ∣ 2^k → 3 ∣ 2`; contradiction.
  replace hk : 3 ∣ 2 ^ k := (by decide : 3 ∣ 9).trans hk
  replace hk : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hk
  revert hk; decide

/-- If `l > 1` and `l` is odd, then `2^l + 1` is not prime. -/
theorem not_prime_two_pow_add_one_of_odd (hl : l > 1) (hl0 : Odd l) :
    ¬Nat.Prime (2 ^ l + 1) := by
  ---- We just observe that `3 ∣ 2^l + 1` and `3 < 2^l + 1`.
  have hl1 : 3 ∣ 2 ^ l + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, ← Nat.div_add_mod l 2, Nat.odd_iff.mp hl0, Nat.pow_succ,
      Nat.pow_mul, ← Nat.mod_add_mod, ← Nat.mod_mul_mod, Nat.pow_mod, Nat.one_pow]
  exact Nat.not_prime_of_dvd_of_lt (m := 3) (n := 2 ^ l + 1) hl1
    (Nat.le_succ 2) (Nat.succ_lt_succ (Nat.pow_lt_pow_right Nat.one_lt_two hl))

/-- If `0 < j ≤ k`, then `2^k + 1 ∤ 2^j - 1`. -/
theorem two_pow_add_one_not_dvd_two_pow_sub_one (hj : j ≠ 0) (h : j ≤ k) :
    ¬2 ^ k + 1 ∣ 2 ^ j - 1 := by
  refine Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt (Nat.one_lt_two_pow hj)) ?_
  calc 2 ^ j - 1
  _ ≤ 2 ^ j := Nat.sub_le (2 ^ j) 1
  _ ≤ 2 ^ k := Nat.pow_le_pow_right Nat.two_pos h
  _ < 2 ^ k + 1 := Nat.lt_succ_self (2 ^ k)

/-- If `k > 0` and `2^{k - 1} + 1 ∣ 2^k - 1`, then `k = 2`. -/
theorem eq_two_of_pow_pred_add_one_dvd_pow_sub_one
    (hk : k > 0) (hk0 : 2 ^ (k - 1) + 1 ∣ 2 ^ k - 1) : k = 2 := by
  have hk1 : 1 < 2 * 2 ^ (k - 1) :=
    Nat.le_mul_of_pos_right 2 (Nat.two_pow_pos (k - 1))
  ---- First, since `2^k - 1 < 2(2^{k - 1} + 1)`, this gives `2^k - 1 = 2^{k - 1} + 1`.
  replace hk0 : 2 * 2 ^ (k - 1) - 1 = 2 ^ (k - 1) + 1 := by
    refine Nat.eq_of_dvd_of_lt_two_mul ?_ ?_ ?_
    · exact Nat.sub_ne_zero_of_lt hk1
    · rwa [← Nat.pow_add_one', Nat.sub_add_cancel hk]
    · exact (Nat.sub_lt_add_one _ _).trans (Nat.lt_succ_self _)
  ---- Now rewriting gives `2^{k - 1} = 2` and thus `k = 2`.
  rw [Nat.sub_eq_iff_eq_add hk1.le, Nat.two_mul, Nat.add_assoc, Nat.add_right_inj] at hk0
  exact Nat.pred_eq_succ_iff.mp (Nat.pow_right_injective (Nat.le_refl 2) hk0)

/-- If `2^k m` is good, where `m > 1`, then `k = 2` and `m = 3`. -/
theorem good_two_pow_mul_odd_imp (hm : Odd m) (hm0 : m > 1) (h : good (2 ^ k * m)) :
    k = 2 ∧ m = 3 := by
  ---- First, there exists a non-negative integer `j ≤ k` such that `m = 2^j - 1`.
  obtain ⟨j, hj, rfl⟩ : ∃ j ≤ k, m = 2 ^ j - 1 := by
    -- Indeed, since `m + 1 > 2` is even, we have `m + 1 ∣ 2^k m ↔ m + 1 ∣ 2^k`.
    have h0 : m + 1 ∣ 2 ^ k * m :=
      (h m (Nat.dvd_mul_left _ _)).resolve_right λ h0 ↦
        hm0.ne.symm (Nat.succ_injective (h0.even_iff.mp hm.add_one))
    replace h0 : m + 1 ∣ 2 ^ k := (Nat.dvd_add_right h0).mp (Nat.dvd_mul_left _ _)
    -- Thus `m + 1 = 2^j` for some `j ≤ k`.
    obtain ⟨j, hj, h1⟩ : ∃ j ≤ k, m + 1 = 2 ^ j :=
      (Nat.dvd_prime_pow Nat.prime_two).mp h0
    exact ⟨j, hj, Nat.eq_sub_of_add_eq h1⟩
  ---- If `k ≤ 2`, then we are done since `2 ≤ j ≤ k`, so now assume that `k > 2`.
  obtain hk | hk : k ≤ 2 ∨ 2 < k := le_or_gt k 2
  · replace hm0 : 2 ≤ j :=
      (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (Nat.add_lt_of_lt_sub hm0)
    obtain rfl : j = 2 := (hj.trans hk).antisymm hm0
    exact ⟨hk.antisymm hj, rfl⟩
  ---- Now the only thing we need from `j` is that `k ≥ j > 0`.
  have hj0 : j ≠ 0 := λ hj0 ↦ hm0.not_ge (hj0 ▸ Nat.zero_le 1)
  clear hm hm0
  ---- For any `l > 1` with `l` odd and `l ≤ k`, we have `2^l + 1 ∣ 2^j - 1`.
  have h0 {l} (hl : l > 1) (hl0 : Odd l) (hl1 : l ≤ k) : 2 ^ l + 1 ∣ 2 ^ j - 1 := by
    ---- Since `2^l ∣ 2^k(2^j - 1)`, `2^l + 1` either divides `2^k(2^j - 1)` or is prime.
    obtain h0 | h0 : 2 ^ l + 1 ∣ 2 ^ k * (2 ^ j - 1) ∨ Nat.Prime (2 ^ l + 1) :=
      h (2 ^ l) (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 hl1) _)
    ---- If `2^l + 1 ∣ 2^k (2^j - 1)`, then `2^l + 1 ∣ 2^j - 1`.
    · have h1 : Nat.Coprime (2 ^ l + 1) 2 := by
        rw [← Nat.coprime_pow_right_iff (Nat.zero_lt_of_lt hl), Nat.coprime_self_add_left]
        exact Nat.coprime_one_left (2 ^ l)
      exact (h1.pow_right k).dvd_of_dvd_mul_left h0
    /- If `2^l + 1` is prime, then we get contradiction, since `l > 1` is odd.
      (See `not_prime_two_pow_add_one_of_odd`.) -/
    · exact absurd h0 (not_prime_two_pow_add_one_of_odd hl hl0)
  ---- Since `2^k + 1 > 2^j - 1 > 0`, `2^k + 1` is prime, so `k` is not odd.
  have hk1 : ¬Odd k := by
    intro h1; replace h1 : 2 ^ k + 1 ∣ 2 ^ j - 1 :=
      h0 (Nat.lt_of_add_left_lt hk) h1 (Nat.le_refl k)
    exact absurd h1 (two_pow_add_one_not_dvd_two_pow_sub_one hj0 hj)
  ---- Then `k - 1` is odd, so `2^{k - 1} + 1 ∣ 2^j - 1`.
  replace h0 : 2 ^ (k - 1) + 1 ∣ 2 ^ j - 1 := by
    refine h0 (Nat.lt_sub_of_add_lt hk) ?_ (Nat.sub_le k 1)
    rwa [← Nat.not_even_iff_odd, ← Nat.even_add_one,
      Nat.sub_add_cancel (Nat.one_le_of_lt hk), ← Nat.not_odd_iff_even]
  ---- Since `2^{k - 1} + 1 > 2^j - 1 > 0` and `j ≤ k`, we have `j = k`.
  replace hj : j = k := hj.eq_of_not_lt λ h1 ↦
    two_pow_add_one_not_dvd_two_pow_sub_one hj0 (Nat.le_sub_one_of_lt h1) h0
  /- Then `2^{k - 1} + 1 ∣ 2^k - 1`, forcing `k = 2`; impossible.
    (See `eq_two_of_pow_pred_add_one_dvd_pow_sub_one`.) -/
  subst j; replace h0 : k = 2 :=
    eq_two_of_pow_pred_add_one_dvd_pow_sub_one (Nat.zero_lt_of_lt hk) h0
  exact absurd h0 hk.ne.symm

/-- Final solution -/
theorem final_solution (hn : n > 0) : good n ↔ (n = 1 ∨ n = 2 ∨ n = 4) ∨ n = 12 := by
  ---- First show that `n = 1, 2, 4, 12` works, by doing direct decision procedure.
  refine Iff.symm ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · -- To make the decision procedure run, we need to add the hypothesis `d ≤ n`.
    intro d hd
    have h : d ≤ n := Nat.le_of_dvd hn hd
    revert hd; revert d
    rcases h with (rfl | rfl | rfl) | rfl
    all_goals decide
  ---- For the other direction, first write `n = 2^k m` with `m` odd.
  obtain ⟨k, m, hm, rfl⟩ : ∃ k m, Odd m ∧ n = 2 ^ k * m :=
    Nat.exists_eq_two_pow_mul_odd hn.ne.symm
  ---- As we have seen, `m = 1` yields `n ∈ {1, 2, 4}`, while `m > 1` yields `m = 12`.
  clear hn
  refine (Nat.eq_or_lt_of_le hm.pos).imp (λ hm0 ↦ ?_) (λ (hm0 : m > 1) ↦ ?_)
  ---- Case 1: `m = 1`, `n ∈ {1, 2, 4}`.
  · subst hm0; rw [Nat.mul_one] at h ⊢
    replace h : k ≤ 2 := good_two_pow_imp h
    revert k; decide
  ---- Case 2: `m > 1`, `n = 12`.
  · obtain ⟨rfl, rfl⟩ : k = 2 ∧ m = 3 := good_two_pow_mul_odd_imp hm hm0 h
    rfl
