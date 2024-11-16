/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.ModEq

/-!
# IMO 2010 N5 (P3)

Given $c ∈ ℕ$, find all functions $f : ℕ → ℕ$ such that
  $(f(m) + n + c)(f(n) + m + c)$ is a square for all $m, n ∈ ℕ$.
-/

namespace IMOSL
namespace IMO2010N5

def good (c : ℕ) (f : ℕ → ℕ) := ∀ m n, ∃ k, (f m + n + c) * (f n + m + c) = k ^ 2

lemma add_right_is_good (c k) : good c (· + k) := by
  intro m n; refine ⟨m + n + k + c, ?_⟩
  rw [Nat.pow_two, m.add_right_comm, n.add_right_comm, n.add_comm]


section

variable (hp : Nat.Prime p) (h : ∃ k : ℕ, a * b = k ^ 2)
include hp h

lemma step1_general (ha : p ^ (2 * n + 1) ∣ a) (ha0 : ¬p ^ (2 * n + 2) ∣ a) : p ∣ b := by
  rcases h with ⟨k, hk⟩
  rcases ha with ⟨u, rfl⟩
  rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm 2, Nat.pow_mul] at hk
  obtain ⟨m, rfl⟩ : p ^ n ∣ k := (Nat.pow_dvd_pow_iff (Nat.succ_ne_zero 1)).mp ⟨_, hk.symm⟩
  rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_right_inj (Nat.pow_pos hp.pos).ne.symm] at hk
  obtain ⟨t, rfl⟩ : p ∣ m := hp.dvd_of_dvd_pow ⟨_, hk.symm⟩
  rw [Nat.mul_pow, p.pow_two, Nat.mul_assoc, Nat.mul_right_inj hp.ne_zero] at hk
  rw [Nat.pow_succ, Nat.mul_dvd_mul_iff_left (Nat.pow_pos hp.pos)] at ha0
  replace hk : p ∣ u ∨ p ∣ b := hp.dvd_mul.mp ⟨t ^ 2, hk⟩
  exact hk.resolve_left ha0

lemma step1_modeq (ha : a ≡ p ^ (2 * n + 1) [MOD p ^ (2 * n + 2)]) : p ∣ b := by
  apply step1_general hp h (n := n)
  · replace ha : (_ % _) % _ = (_ % _) % _ := congrArg (· % (p ^ (2 * n + 1))) ha
    rw [Nat.pow_succ, Nat.mod_mul_right_mod, Nat.mod_mul_right_mod, Nat.mod_self] at ha
    exact Nat.dvd_of_mod_eq_zero ha
  · rw [Nat.dvd_iff_mod_eq_zero, ha, ← Nat.dvd_iff_mod_eq_zero, Nat.pow_succ]
    have h0 : 0 < p ^ (2 * n + 1) := Nat.pow_pos hp.pos
    exact Nat.not_dvd_of_pos_of_lt h0 ((Nat.lt_mul_iff_one_lt_right h0).mpr hp.one_lt)

lemma step1_pow_one (ha : a ≡ p [MOD p ^ 2]) : p ∣ b :=
  step1_modeq hp h (n := 0) (p.pow_one.symm ▸ ha)

end


lemma exists_add_modeq (hb : 0 < b) (k a) : ∃ n, k + n ≡ a [MOD b] := by
  refine ⟨(b - 1) * k + a, ?_⟩
  rw [Nat.add_left_comm, ← Nat.add_assoc, ← Nat.succ_mul, ← Nat.pred_eq_sub_one,
    Nat.succ_pred_eq_of_pos hb, Nat.ModEq, Nat.mul_add_mod]

lemma step2 (hf : good c f) (hp : Nat.Prime p) (h : f k ≡ f l [MOD p]) : k ≡ l [MOD p] := by
  suffices ∃ n, p ∣ f n + k + c ∧ p ∣ f n + l + c by
    rcases this with ⟨n, hn⟩
    replace hn : (f n + k + c) ≡ (f n + l + c) [MOD p] := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero] at hn
      exact hn.1.trans hn.2.symm
    exact (hn.add_right_cancel' _).add_left_cancel' _
  ---- Now find one such `n`, depending on whether `f(k) ≡ f(l) (mod p^2)` or not
  by_cases h0 : f k ≡ f l [MOD p ^ 2]
  ---- Case 1: `f(k) ≡ f(l) (mod p^2)`
  · obtain ⟨n, h1⟩ : ∃ n, f k + c + n ≡ p [MOD p ^ 2] :=
      exists_add_modeq (Nat.pow_pos hp.pos) _ _
    replace h0 : f l + c + n ≡ p [MOD p ^ 2] :=
      ((h0.add_right c).add_right n).symm.trans h1
    rw [Nat.add_right_comm] at h0 h1
    exact ⟨n, step1_pow_one hp (hf k n) h1, step1_pow_one hp (hf l n) h0⟩
  ---- Case 2: `¬f(k) ≡ f(l) (mod p^2)`
  · obtain ⟨n, h1⟩ : ∃ n, f k + c + n ≡ p ^ 3 [MOD p ^ 4] :=
      exists_add_modeq (Nat.pow_pos hp.pos) _ _
    rw [Nat.add_right_comm] at h1
    refine ⟨n, step1_modeq hp (hf k n) (n := 1) h1, step1_general hp (hf l n) (n := 0) ?_ ?_⟩
    · replace h1 : _ % _ = _ % _ := congrArg (· % p) h1
      rw [Nat.pow_succ, Nat.mod_mul_left_mod, Nat.mod_mul_left_mod,
        Nat.pow_succ, Nat.mul_mod_left, (h.add_right n).add_right c] at h1
      rw [Nat.pow_one, Nat.dvd_iff_mod_eq_zero, h1]
    · intro h2; replace h2 : (f l + n + c) % p ^ 2 = 0 := Nat.mod_eq_zero_of_dvd h2
      replace h1 : _ % _ = _ % _ := congrArg (· % p ^ 2) h1
      rw [p.pow_add 2 2, Nat.mod_mul_left_mod, Nat.mod_mul_left_mod,
        p.pow_succ 2, Nat.mul_mod_right, ← h2, ← Nat.ModEq] at h1
      exact h0 ((h1.add_right_cancel' _).add_right_cancel' _)

lemma not_modeq_prime_imp₁ (h : k ≤ l) (h0 : ∀ p, p.Prime → ¬k ≡ l [MOD p]) : l = k + 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, l = k + c := Nat.exists_eq_add_of_le h
  refine congrArg (k + ·) ((dec_em (c = 1)).resolve_right λ h1 ↦ ?_)
  exact h0 _ (Nat.minFac_prime h1) ((c.minFac_dvd.zero_modEq_nat).add_left k)

lemma not_modeq_prime_imp₂ (h : ∀ p, p.Prime → ¬k ≡ l [MOD p]) : l = k + 1 ∨ k = l + 1 :=
  (Nat.le_total k l).imp (λ h0 ↦ not_modeq_prime_imp₁ h0 h)
    (λ h0 ↦ not_modeq_prime_imp₁ h0 λ p hp h1 ↦ h p hp h1.symm)

lemma step3 {f : ℕ → ℕ} (hf : ∀ {p k l}, p.Prime → f k ≡ f l [MOD p] → k ≡ l [MOD p]) :
    ∃ k, f = (· + k) := by
  have hf0 : f.Injective := λ k l h ↦ by
    obtain ⟨p, hp0, hp⟩ : ∃ p > max k l, p.Prime :=
      Nat.exists_infinite_primes (max k l).succ
    rw [gt_iff_lt, max_lt_iff] at hp0
    replace hf : k % p = l % p := hf hp (congrArg (· % p) h)
    rwa [Nat.mod_eq_of_lt hp0.1, Nat.mod_eq_of_lt hp0.2] at hf
  have h (n) : f (n + 1) = f n + 1 ∨ f n = f (n + 1) + 1 := by
    refine not_modeq_prime_imp₂ λ p hp h ↦ Nat.zero_ne_one ?_
    replace h : 0 % p = 1 % p := (hf hp h).add_left_cancel'
    rwa [Nat.zero_mod, Nat.mod_eq_of_lt hp.one_lt] at h
  have h0 {n} (hn : f n = f (n + 1) + 1) : f (n + 1) = f (n + 2) + 1 :=
    (h _).resolve_left λ h0 ↦ (hf0 (h0.trans hn.symm)).not_gt (n + 1).le_succ
  replace h0 (n) : f (n + 1) = f n + 1 := by
    refine (h n).resolve_right λ hn ↦ ?_
    replace h0 : ∀ k, f (n + k) = f (n + k + 1) + 1 := Nat.rec hn λ k ↦ h0
    replace h0 : ∀ k, f n = f (n + k) + k :=
      Nat.rec rfl λ k hk ↦ by rw [hk, h0, Nat.add_right_comm]; rfl
    exact (h0 (f n + 1)).not_lt (Nat.le_add_left _ _)
  refine ⟨f 0, funext (Nat.rec (f 0).zero_add.symm λ k hk ↦ ?_)⟩
  rw [h0, hk, Nat.add_right_comm]

/-- Final solution -/
theorem final_solution : good c f ↔ ∃ k, f = (· + k) :=
  ⟨λ h ↦ step3 (step2 h), λ ⟨_, h⟩ ↦ h ▸ add_right_is_good _ _⟩
