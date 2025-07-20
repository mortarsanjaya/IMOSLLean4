/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Basic

/-!
# IMO 2016 N4

Consider some $k, ℓ, m, n ∈ ℕ^+$ with $n > 1$ such that
$$ n^k + mn^ℓ + 1 ∣ n^{k + ℓ} - 1. $$
Prove that one of the following holds:
* $m = 1$ and $ℓ = 2k$; or
* $k = (t + 1)ℓ$ and $m(n^ℓ - 1) = n^{t ℓ} - 1$ for some $t > 0$.
-/

namespace IMOSL
namespace IMO2016N4

lemma dvd_of_pow_sub_one_dvd (hn : 1 < n) (h : n ^ k - 1 ∣ n ^ l - 1) : k ∣ l := by
  ---- Change the goal to `n^{l % k} - 1 = 0`
  suffices h0 : n ^ (l % k) - 1 = 0 by
    refine Nat.dvd_of_mod_eq_zero ((eq_or_ne _ _).resolve_right λ h1 ↦ absurd ?_ h0.not_gt)
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow h1 hn)
  ---- Obtain `n^l ≡ 1 (mod n^k - 1)`
  have h0 (c) : 0 < n ^ c := Nat.pow_pos (Nat.zero_lt_of_lt hn)
  obtain ⟨x, hx⟩ : ∃ x, n ^ k = x + 1 := Nat.exists_eq_add_of_le' (h0 k)
  replace h : n ^ l % x = 1 % x := by
    obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le' (h0 l)
    rw [hx, Nat.add_sub_cancel, hy, Nat.add_sub_cancel] at h
    rw [hy, ← Nat.mod_add_mod, Nat.mod_eq_zero_of_dvd h]
  ---- Manipulate to `n^{l % k} ≡ 1 (mod n^k - 1)`
  rw [← Nat.div_add_mod l k, Nat.pow_add, Nat.pow_mul, ← Nat.mod_mul_mod, Nat.pow_mod,
    hx, Nat.add_mod_left, ← Nat.pow_mod, Nat.one_pow, Nat.mod_mul_mod, Nat.one_mul] at h
  replace h : x ∣ n ^ (l % k) - 1 :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)
  obtain rfl : x = n ^ k - 1 := Nat.eq_sub_of_add_eq hx.symm
  ---- If `k = 0`, we're done. if `k > 0`, then `l % k < k` and done again.
  clear hx; obtain rfl | hk : k = 0 ∨ 0 < k := k.eq_zero_or_pos
  · exact Nat.eq_zero_of_zero_dvd h
  · refine Nat.eq_zero_of_dvd_of_lt h (Nat.sub_lt_sub_right (h0 _) ?_)
    exact Nat.pow_lt_pow_right hn (Nat.mod_lt l hk)

/-- Final solution -/
theorem final_solution (hk : 0 < k) (hl : 0 < l) (hm : 0 < m) (hn : 1 < n)
    (h : n ^ k + m * n ^ l + 1 ∣ n ^ (k + l) - 1) :
    (m = 1 ∧ l = 2 * k) ∨ (∃ t > 0, k = (t + 1) * l ∧ m * (n ^ l - 1) = n ^ (l * t) - 1) := by
  have hn' : 0 < n := Nat.zero_lt_of_lt hn
  replace h : n ^ k + m * n ^ l + 1 ∣ n ^ k + m * n ^ l + n ^ (k + l) := by
    have X : 1 ≤ n ^ (k + l) := Nat.pow_pos hn'
    rwa [← Nat.dvd_add_self_right, Nat.add_left_comm, Nat.sub_add_cancel X] at h
  have h0 : (n ^ k + m * n ^ l + 1).Coprime n := by
    obtain ⟨N, h0⟩ : n ∣ n ^ k + m * n ^ l := by
      refine ⟨n ^ (k - 1) + m * n ^ (l - 1), ?_⟩
      rw [n.mul_add, ← n.pow_add_one', Nat.sub_add_cancel hk,
        n.mul_left_comm,← n.pow_add_one', Nat.sub_add_cancel hl]
    rw [h0, Nat.coprime_mul_left_add_left]
    exact n.gcd_one_left
  refine (le_or_gt k l).imp (λ h1 ↦ ?_) (λ h1 ↦ ?_)
  ---- Case 1: `l ≥ k`
  · obtain ⟨l', rfl⟩ : ∃ l', l = k + l' := Nat.exists_eq_add_of_le h1
    replace h1 : n ^ k + m * n ^ (k + l') + n ^ (k + (k + l'))
        = n ^ k * (n ^ (k + l') + m * n ^ l' + 1) := by
      rw [n.pow_add, m.mul_left_comm, n.pow_add, Nat.add_assoc, ← Nat.mul_add,
        Nat.add_comm, ← Nat.mul_succ, ← n.pow_add, Nat.add_comm]
    replace h : n ^ k + m * n ^ (k + l') + 1 ∣ n ^ (k + l') + m * n ^ l' + 1 := by
      rwa [h1, (h0.pow_right k).dvd_mul_left] at h
    replace h1 {a} (ha : 0 < a) : a + 1 ≤ 2 * a := by
      rwa [Nat.two_mul, Nat.add_le_add_iff_left]
    replace h : n ^ (k + l') + m * n ^ l' = n ^ k + m * n ^ (k + l') := by
      refine Nat.add_left_inj.mp (Nat.eq_of_dvd_of_lt_two_mul (Nat.succ_ne_zero _) h ?_)
      calc
        _ ≤ (m + 1) * n ^ (k + l') + 1 := by
          rw [Nat.add_le_add_iff_right, Nat.add_comm, m.succ_mul]
          refine Nat.add_le_add_right (Nat.mul_le_mul_left m ?_) _
          exact Nat.pow_le_pow_right hn' (l'.le_add_left k)
        _ < 2 * (m * n ^ (k + l') + 1) := by
          rw [← Nat.succ_le_iff, Nat.mul_succ 2, ← Nat.mul_assoc]
          exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (h1 hm)) 2
        _ ≤ _ := Nat.mul_le_mul_left 2 (Nat.succ_le_succ (Nat.le_add_left _ _))
    obtain rfl : m = 1 := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := Nat.exists_eq_add_of_le' hm
      refine m'.eq_zero_or_pos.elim (congrArg Nat.succ) λ h2 ↦ absurd ?_ h.not_lt
      calc
        _ ≤ n ^ (k + l') + n ^ k * m' * n ^ l' := by
          refine Nat.add_le_add_left (Nat.mul_le_mul_right _ ((h1 h2).trans ?_)) _
          exact Nat.mul_le_mul_right _ (hn.trans_le (Nat.le_self_pow hk.ne.symm n))
        _ = (m' + 1) * n ^ (k + l') := by
          rw [Nat.mul_right_comm, ← Nat.pow_add, Nat.add_comm, ← Nat.mul_succ, mul_comm]
        _ < _ := Nat.lt_add_of_pos_left (Nat.pow_pos hn')
    rw [Nat.one_mul, Nat.one_mul, Nat.add_comm, Nat.add_left_inj] at h
    refine ⟨rfl, ?_⟩; rw [Nat.two_mul, Nat.pow_right_injective hn h]
  ---- Case 2: `l < k`
  · obtain ⟨k', rfl⟩ : ∃ k', k = l + k' := Nat.exists_eq_add_of_le h1.le
    replace h1 : n ^ (l + k') + m * n ^ l + n ^ (l + k' + l)
        = n ^ l * (n ^ (l + k') + n ^ k' + m) := by
      rw [← add_rotate, Nat.pow_add, Nat.mul_comm, Nat.pow_add,
        ← Nat.mul_add, m.mul_comm, ← Nat.mul_add]
    replace h : n ^ (l + k') + m * n ^ l + 1 ∣ n ^ (l + k') + n ^ k' + m := by
      rwa [h1, (h0.pow_right l).dvd_mul_left] at h
    replace h : n ^ (l + k') + n ^ k' + m = n ^ (l + k') + m * n ^ l + 1 := by
      apply Nat.eq_of_dvd_of_lt_two_mul (Nat.add_pos_right _ hm).ne.symm h
      calc
        _ < 2 * (n ^ (l + k') + m) := by
          rw [Nat.two_mul, Nat.add_right_comm, Nat.add_lt_add_iff_left]
          exact Nat.lt_add_right m (Nat.pow_lt_pow_right hn (Nat.lt_add_of_pos_left hl))
        _ < _ := by
          refine Nat.mul_lt_mul_of_pos_left ?_ Nat.two_pos
          rw [Nat.lt_succ_iff, Nat.add_le_add_iff_left]
          exact Nat.le_mul_of_pos_right _ (Nat.pow_pos hn')
    replace h : n ^ k' - 1 = m * (n ^ l - 1) := by
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_right_inj] at h
      apply congrArg (· - (m + 1)) at h
      rwa [Nat.add_sub_add_right, Nat.add_comm, Nat.add_sub_add_left, ← Nat.mul_sub_one] at h
    obtain ⟨t, rfl⟩ : l ∣ k' := dvd_of_pow_sub_one_dvd hn ⟨m, h.trans (Nat.mul_comm _ _)⟩
    refine ⟨t, ?_, ?_, h.symm⟩
    · apply Nat.pos_of_ne_zero; rintro rfl
      rw [Nat.mul_zero, Nat.pow_zero, Nat.zero_eq_mul] at h
      exact h.elim hm.ne.symm (Nat.zero_lt_sub_of_lt (Nat.one_lt_pow hl.ne.symm hn)).ne.symm
    · rw [Nat.add_comm, Nat.mul_comm, t.succ_mul]
