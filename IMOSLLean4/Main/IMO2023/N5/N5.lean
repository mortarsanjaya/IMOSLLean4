/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Find

/-!
# IMO 2023 N5

Let $(a_n)_{n ≥ 0}$ be a strictly increasing sequence of positive integers such that:
* $a_k ∣ 2(a_0 + a_1 + … + a_{k - 1})$ for all $k ∈ ℕ$;
* for each prime $p$, there exists $k ∈ ℕ$ such that $p ∣ a_k$.

Prove that for any $n ∈ ℕ^+$, there exists $k ∈ ℕ$ such that $n ∣ a_k$.
-/

namespace IMOSL
namespace IMO2023N5

open Finset

structure goodSeq where
  a : ℕ → ℕ
  a_strictMono : StrictMono a
  a_pos : ∀ k, 0 < a k
  a_spec : ∀ k, a k ∣ 2 * ∑ i ∈ range k, a i
  exists_dvd_a_of_prime : ∀ p : ℕ, p.Prime → ∃ k, p ∣ a k


namespace goodSeq

variable (X : goodSeq)

def b (k : ℕ) : ℕ := (2 * ∑ i ∈ range k, X.a i) / X.a k

lemma b_zero : X.b 0 = 0 := by
  rw [b, sum_range_zero, Nat.mul_zero, Nat.zero_div]

lemma b_spec (k) : X.b k * X.a k = 2 * ∑ i ∈ range k, X.a i :=
  Nat.div_mul_cancel (X.a_spec k)

lemma b_succ_pos (k) : 0 < X.b (k + 1) := by
  apply Nat.pos_of_mul_pos_right (b := X.a (k + 1))
  rw [X.b_spec, sum_range_succ]
  exact Nat.mul_pos Nat.two_pos (Nat.add_pos_right _ (X.a_pos k))

lemma b_formula (k) : X.b (k + 1) * X.a (k + 1) = (X.b k + 2) * X.a k := by
  rw [X.b_spec, Nat.add_mul, X.b_spec, sum_range_succ, Nat.mul_add]

lemma b_succ_le (k) : X.b (k + 1) ≤ X.b k + 1 :=
  Nat.le_of_lt_succ <| Nat.lt_of_not_le λ h ↦ (X.b_formula k).not_gt <|
    Nat.mul_lt_mul_of_le_of_lt h (X.a_strictMono k.lt_succ_self) (X.b_succ_pos k)

lemma b_not_bdd (M) : ∃ k, M ≤ X.b k := by
  by_contra h; simp only [not_exists, not_le] at h
  obtain ⟨p, ha0p, hMp, hp⟩ : ∃ p : ℕ, X.a 0 < p ∧ M + 2 ≤ p ∧ p.Prime := by
    obtain ⟨p, h0, hp⟩ := (max (X.a 0).succ (M + 2)).exists_infinite_primes
    exact ⟨p, le_of_max_le_left h0, le_of_max_le_right h0, hp⟩
  obtain ⟨k, hk⟩ : ∃ k, p ∣ X.a k := X.exists_dvd_a_of_prime p hp
  revert ha0p; refine (Nat.le_of_dvd (X.a_pos 0) ?_).not_gt
  ---- Now we have `b_n + 2 < M + 2 ≤ p` for all `n` and `p ∣ a_k`, and the goal is `p ∣ a_0`
  refine Nat.decreasingInduction (λ k _ hk ↦ ?_) hk k.zero_le
  have h0 : p ∣ X.b k + 2 ∨ p ∣ X.a k := hp.dvd_mul.mp (X.b_formula _ ▸ hk.mul_left _)
  refine h0.resolve_left (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) ?_)
  exact (Nat.add_lt_add_right (h k) 2).trans_le hMp

lemma exists_dvd_a_of_pos (hN : 0 < N) : ∃ k, N ∣ X.a k := by
  obtain ⟨k, hk, hk0⟩ : ∃ k, X.b (k + 1) = N ∧ X.b k + 1 = N := by
    have h : ∃ k, N ≤ X.b k := X.b_not_bdd N
    have h0 := Nat.find_spec h
    obtain ⟨k, h1⟩ : ∃ k, Nat.find h = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero λ h1 ↦ h0.not_gt (h1 ▸ X.b_zero.trans_lt hN)
    have h2 := Nat.lt_of_not_le (Nat.find_min h (k.lt_succ_self.trans_eq h1.symm))
    have h3 : X.b (k + 1) ≤ X.b k + 1 := X.b_succ_le k
    replace h0 : X.b (k + 1) = N := Nat.le_antisymm (h3.trans h2) (h1 ▸ h0)
    exact ⟨k, h0, Nat.le_antisymm h2 (h3.trans_eq' h0.symm)⟩
  refine ⟨k, (Nat.dvd_add_right ⟨X.a k, rfl⟩).mp ⟨X.a (k + 1), ?_⟩⟩
  calc _ = (X.b k + 1 + 1) * X.a k := by rw [hk0, Nat.succ_mul]
       _ = _ := by rw [← X.b_formula, hk]

end goodSeq





/-- Final solution -/
alias final_solution := goodSeq.exists_dvd_a_of_pos
