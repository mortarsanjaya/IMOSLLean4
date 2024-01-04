/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Nat.Lemma2
import Mathlib.Data.Nat.Log

/-!
# IMO 2020 N5, ℕ-version (Lemma 3)

This file proves the following lemma:
* Let `f : MulMap M` and `p : ℕ` be a prime.
  Then `p^k` is `f`-good for all `k ≥ 0` iff `f(p - 1) = 0` and
    `f(n) = f(n % p)` for any `n : ℕ` such that `¬p ∣ n`.
The forward direction is essentially Lemma 3 from the LaTeX file.
-/

namespace IMOSL
namespace IMO2020N5
namespace Nat

variable [CancelCommMonoid M] {f : MulMap M} (h : Nat.Prime p)

theorem nice_pow_map_eq_mod (h0 : ∀ k, nice f (p ^ k)) (h1 : ¬p ∣ m) :
    f m = f (m % p) := by
  ---- Strong induction on `m`; base case `m < p` is easy
  induction' m using Nat.strong_induction_on with m₀ ih_m₀
  rcases lt_or_le m₀ p with h2 | h2
  · exact congr_arg _ (Nat.mod_eq_of_lt h2).symm
  ---- Case `m ≥ p`: Collect some results
  let q := p ^ (p.log m₀ + 1) / m₀
  let r := p ^ (p.log m₀ + 1) % m₀
  have m₀_pos : 0 < m₀ := h.pos.trans_le h2
  have q_pos : 0 < q :=
    Nat.div_pos (Nat.lt_pow_succ_log_self h.one_lt m₀).le m₀_pos
  replace h2 : 0 < p.log m₀ := Nat.log_pos_iff.mpr ⟨h2, h.one_lt⟩
  have q_lt_p : q < p := by
    rw [Nat.div_lt_iff_lt_mul m₀_pos, pow_succ]
    exact Nat.mul_lt_mul_of_pos_left
      ((Nat.pow_log_le_self p m₀_pos.ne.symm).lt_of_ne
        λ h3 ↦ h1 <| h3 ▸ dvd_pow_self p h2.ne.symm) h.pos
  have p_nmid_q : ¬p ∣ q := Nat.not_dvd_of_pos_of_lt q_pos q_lt_p
  have X : r + m₀ * q = p ^ _ := Nat.mod_add_div (p ^ (p.log m₀ + 1)) m₀
  have X0 : p ∣ r + m₀ * q := X ▸ dvd_pow_self p (Nat.log p m₀).succ_ne_zero
  have p_nmid_m₀q : ¬p ∣ m₀ * q := h.not_dvd_mul h1 p_nmid_q
  have p_nmid_r : ¬p ∣ r := λ h3 ↦
    p_nmid_m₀q <| (Nat.dvd_add_iff_right h3).mpr X0
  have r_mod_p_pos : 0 < r % p := Nat.emod_pos_of_not_dvd p_nmid_r
  have r_pos : 0 < r := r_mod_p_pos.trans_le (r.mod_le p)
  ---- Now ready for the goal
  specialize ih_m₀ r (Nat.mod_lt _ m₀_pos) p_nmid_r
  have X1 : nice f p := p.pow_one ▸ h0 1
  rw [h0 _ _ _ r_pos (Nat.mul_pos m₀_pos q_pos) X, f.map_mul m₀_pos q_pos,
    X1 _ _ r_mod_p_pos (Nat.emod_pos_of_not_dvd p_nmid_m₀q)
      (mod_add_mod_eq_of_dvd_add_of_not_dvd X0 p_nmid_r),
    nice_mul_mod_of_not_dvd h X1 h1 p_nmid_q,
    Nat.mod_eq_of_lt q_lt_p] at ih_m₀
  exact mul_left_injective _ ih_m₀

theorem nice_of_map_pred_and_map_eq_mod
    (h0 : f (p - 1) = 1) (h1 : ∀ m, ¬p ∣ m → f m = f (m % p)) :
    nice f p := λ a b ha hb h2 ↦ by
  have a_lt_p := (Nat.lt_add_of_pos_right hb).trans_eq h2
  have p_nmid_a := Nat.not_dvd_of_pos_of_lt ha a_lt_p
  have h3 : a % p + a * (p - 1) % p = p := by
    refine mod_add_mod_eq_of_dvd_add_of_not_dvd ⟨a, ?_⟩ p_nmid_a
    rw [← mul_one_add, Nat.add_sub_cancel' h.one_lt.le, mul_comm]
  rw [← h3, Nat.mod_eq_of_lt a_lt_p, add_right_inj] at h2
  have p_pred_pos : 0 < p - 1 := h.pred_pos
  rw [h2, ← mul_one (f a), ← h0, ← f.map_mul ha p_pred_pos]
  exact h1 (a * (p - 1)) (h.not_dvd_mul p_nmid_a <|
    Nat.not_dvd_of_pos_of_lt p_pred_pos (Nat.pred_lt_self h.pos))

theorem nice_pow_of_map_pred_and_map_eq_mod
    (h0 : f (p - 1) = 1) (h1 : ∀ m, ¬p ∣ m → f m = f (m % p)) :
    ∀ k, nice f (p ^ k) :=
  Nat.rec (nice_one _) λ k nice_p_k a b ha hb h2 ↦ by
    ---- Induction step
    have p_dvd_a_add_b : p ∣ a + b := ⟨p ^ k, h2.trans Nat.pow_succ'⟩
    by_cases h3 : p ∣ a
    -- Case 1: `p ∣ a`
    · obtain ⟨b₀, rfl⟩ : p ∣ b := (Nat.dvd_add_iff_right h3).mpr p_dvd_a_add_b
      rcases h3 with ⟨a₀, rfl⟩
      rw [CanonicallyOrderedCommSemiring.mul_pos] at ha hb
      rw [← mul_add, pow_succ, Nat.mul_left_cancel_iff h.pos] at h2
      rw [f.map_mul ha.1 ha.2, f.map_mul ha.1 hb.2]
      exact congr_arg _ (nice_p_k _ _ ha.2 hb.2 h2)
    -- Case 2: `¬p ∣ a`
    · have h4 : ¬p ∣ b := λ h4 ↦ h3 ((Nat.dvd_add_left h4).mp p_dvd_a_add_b)
      rw [h1 a h3, h1 b h4]
      exact nice_of_map_pred_and_map_eq_mod h h0 h1 _ _
        (Nat.emod_pos_of_not_dvd h3) (Nat.emod_pos_of_not_dvd h4)
        (mod_add_mod_eq_of_dvd_add_of_not_dvd p_dvd_a_add_b h3)

theorem nice_pow_iff :
    (∀ k, nice f (p ^ k)) ↔ (f (p - 1) = 1 ∧ ∀ m, ¬p ∣ m → f m = f (m % p)) :=
  ⟨λ h0 ↦ ⟨nice_map_pred h (p.pow_one ▸ h0 1), λ _ ↦ nice_pow_map_eq_mod h h0⟩,
  λ h0 ↦ nice_pow_of_map_pred_and_map_eq_mod h h0.1 h0.2⟩
