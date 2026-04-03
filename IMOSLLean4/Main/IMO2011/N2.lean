/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Factorization.Defs

/-!
### IMO 2011 N2

Let $d_1, d_2, …, d_9$ be distinct integers.
Prove that there exists an integer $N$ such that for any integer $x ≥ N$,
  at least one of $d_1, d_2, …, d_9$ is divisible by a prime greater than $20$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2011SL.pdf).
-/

namespace IMOSL
namespace IMO2011N2

open Finset

/-- Let `S, T ⊆ ℕ` be finite sets of with `#T ≤ #S`. Then there exists `N : ℕ` such that
  for any `x ≥ N`, there exists a prime `p ∉ T` and some `d ∈ S` such that `p ∣ x + d`. -/
theorem general_result_Nat {S T : Finset ℕ} (h : #T < #S) :
    ∃ N, ∀ x ≥ N, ∃ p ∉ T, Nat.Prime p ∧ ∃ d ∈ S, (p : ℕ) ∣ x + d := by
  have hS : S.Nonempty := card_ne_zero.mp (Nat.ne_zero_of_lt h)
  ---- WLOG assume that `T` only consists of primes.
  wlog hT : ∀ p ∈ T, Nat.Prime p generalizing T
  · obtain ⟨N, hN⟩ :
        ∃ N, ∀ x ≥ N, ∃ p ∉ T.filter Nat.Prime, Nat.Prime p ∧ ∃ d ∈ S, p ∣ x + d :=
      this ((T.card_filter_le Nat.Prime).trans_lt h) (λ p hp ↦ (mem_filter.mp hp).2)
    refine ⟨N, λ x hx ↦ ?_⟩
    obtain ⟨p, hp, hp0⟩ := hN x hx
    rw [mem_filter, and_iff_left hp0.1] at hp
    exact ⟨p, hp, hp0⟩
  ---- We claim that `N = m^{#T} + 1` works where `m : ℕ` satisfies `m > d` for any `d ∈ S`.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ d : S, d < m :=
    ⟨S.max' hS + 1, λ d ↦ Nat.lt_succ_of_le (S.le_max' d.1 d.2)⟩
  refine ⟨m ^ #T + 1, λ x (hx : m ^ #T < x) ↦ ?_⟩
  /- Suppose for the sake of contradiction that there exists `x > m^{#T}`
    such that for any `d ∈ S`, all prime factors of `x + d` are in `T`. -/
  by_contra! h0
  replace h0 (d : S) : (x + d).primeFactors ⊆ T := by
    intro p hp; by_contra hp0
    exact h0 p hp0 (Nat.prime_of_mem_primeFactors hp) d d.2 (Nat.dvd_of_mem_primeFactors hp)
  /- Then there exists a function `f : S → T` such that
    `f(d)^{ν_{f(d)}(x + d)} > m` for all `d ∈ S`. -/
  obtain ⟨f, hf⟩ : ∃ f : S → T, ∀ d, m < ordProj[f d] (x + d) := by
    suffices ∀ d : S, ∃ p : T, m < ordProj[p] (x + d) from Classical.axiomOfChoice this
    intro d; have hxd : m ^ #T < x + d := Nat.lt_add_right d hx
    replace hxd : ∏ i ∈ T, m < ∏ p ∈ T, ordProj[p] (x + d) := calc
      _ = m ^ #T := prod_const m
      _ < x + d := hxd
      _ = ∏ p ∈ (x + d).primeFactors, ordProj[p] (x + d) :=
        (Nat.prod_factorization_pow_eq_self (Nat.ne_zero_of_lt hxd)).symm
      _ ≤ ∏ p ∈ T, ordProj[p] (x + d) :=
        prod_le_prod_of_subset_of_one_le' (h0 d) (λ p hp _ ↦ Nat.pow_pos (hT p hp).pos)
    obtain ⟨p, hp, hp0⟩ : ∃ p ∈ T, m < ordProj[p] (x + d) := exists_lt_of_prod_lt' hxd
    exact ⟨⟨p, hp⟩, hp0⟩
  /- Since `#T < #S`, `f` is not injective, say `f(d₁) = f(d₂) = p` with `d₁ ≠ d₂`.
    (After `mathlib` update, should try using `Fintype.not_injective_of_card_lt`.) -/
  replace h0 : ¬f.Injective := λ hf0 ↦ h.not_ge (card_le_card_of_injective hf0)
  replace h0 : ∃ d₁ d₂, f d₁ = f d₂ ∧ d₁ ≠ d₂ := by
    simpa only [Function.Injective, not_forall, exists_prop] using h0
  rcases h0 with ⟨d₁, d₂, hd0, hd⟩
  ---- WLOG assume `d₁ < d₂`.
  wlog hd1 : d₁ < d₂ generalizing d₁ d₂
  · exact this d₂ d₁ hd0.symm hd.symm (lt_of_le_of_ne (not_lt.mp hd1) hd.symm)
  ---- Setting `k = min(ν_p(x + d₁), ν_p(x + d₂))`, we have `p^k ∣ m`.
  set p : ↥T := f d₂
  let k : ℕ := min ((x + d₁).factorization p) ((x + d₂).factorization p)
  replace hf : m < p ^ k := by
    obtain h0 | h0 : k = (x + d₁).factorization p ∨ k = (x + d₂).factorization p :=
      Std.MinEqOr.min_eq_or _ _
    · rw [h0, ← hd0]; exact hf d₁
    · rw [h0]; exact hf d₂
  ---- Also, `p^k` divides `x + d₁` and `x + d₂`, and so `p^k ∣ d₂ - d₁`.
  replace hd₁ : (p : ℕ) ^ k ∣ x + d₁ := calc
    _ ∣ ordProj[(p : ℕ)] (x + d₁) := Nat.pow_dvd_pow _ (Nat.min_le_left _ _)
    _ = ordProj[(f d₁ : ℕ)] (x + d₁) := by rw [← hd0]
    _ ∣ x + d₁ := Nat.ordProj_dvd _ _
  have hd₂ : (p : ℕ) ^ k ∣ x + d₂ := calc
    _ ∣ ordProj[(p : ℕ)] (x + d₂) := Nat.pow_dvd_pow _ (Nat.min_le_right _ _)
    _ ∣ x + d₂ := Nat.ordProj_dvd _ _
  replace hd : (p : ℕ) ^ k ∣ d₂ - d₁ := calc
    _ ∣ (x + d₂) - (x + d₁) := Nat.dvd_sub hd₂ hd₁
    _ = d₂ - d₁ := Nat.add_sub_add_left _ _ _
  clear hd₁ hd₂ hd0 hx; clear_value k p
  --- But then `m < p^k ≤ |d₁ - d₂| < m`; contradiction.
  have h0 : m < m := calc
    _ < (p : ℕ) ^ k := hf
    _ ≤ d₂ - d₁ := Nat.le_of_dvd (Nat.zero_lt_sub_of_lt hd1) hd
    _ < m := Nat.sub_lt_of_lt (hm d₂)
  exact Nat.lt_irrefl m h0

/-- Let `S ⊆ ℤ` and `T ⊆ ℕ` be a finite set with `#T < #S`. Then there exists `N : ℕ` such
  that for any `x ≥ N`, there exists a prime `p ∉ T` and some `d ∈ S` with `p ∣ x + d`. -/
theorem general_result_Int {S : Finset ℤ} {T : Finset ℕ} (h : #T < #S) :
    ∃ N, ∀ x ≥ N, ∃ p ∉ T, Nat.Prime p ∧ ∃ d ∈ S, (p : ℤ) ∣ x + d := by
  ---- Pick some integer `m` such that `m + d ≥ 0` for any `d ∈ S`.
  obtain ⟨m, hm⟩ : ∃ m, ∀ d ∈ S, 0 ≤ m + d := by
    refine ⟨-S.min' (card_ne_zero.mp (Nat.ne_zero_of_lt h)), λ d hd ↦ ?_⟩
    rw [neg_add_eq_sub, Int.sub_nonneg]
    exact S.min'_le d hd
  ---- Apply `general_result_Nat` on `S' = m + S`.
  obtain ⟨S', rfl⟩ : ∃ S' : Finset ℕ, S'.image (λ d : ℕ ↦ (d : ℤ) - m) = S := by
    refine ⟨(S.image (m + ·)).image Int.natAbs, ext λ x ↦ ?_⟩
    simp_rw [mem_image, exists_exists_and_eq_and, ← exists_prop]
    conv_lhs => right; ext; right; ext h0
                rw [← Int.eq_natAbs_of_nonneg (hm _ h0), add_sub_cancel_left]
    simp_rw [exists_prop, exists_eq_right]
  replace h : #T < #S' := calc
    _ < #(S'.image (λ d : ℕ ↦ (d : ℤ) - m)) := h
    _ = #S' := card_image_of_injective _ λ _ _ h0 ↦ by
      rwa [Int.sub_left_inj, Int.natCast_inj] at h0
  obtain ⟨N, hN⟩ : ∃ N, ∀ x ≥ N, ∃ p ∉ T, Nat.Prime p ∧ ∃ d ∈ S', (p : ℕ) ∣ x + d :=
    general_result_Nat h
  clear h hm
  ---- Then add `m` from the resulting `N` to get the desired `N`.
  refine ⟨m + N, λ x hx ↦ ?_⟩
  replace hx : (N : ℤ) ≤ x - m := Int.le_sub_left_of_add_le hx
  have hx0 : 0 ≤ x - m := (Int.natCast_nonneg N).trans hx
  replace hx0 : x - m = (x - m).natAbs := Int.eq_natAbs_of_nonneg hx0
  obtain ⟨p, hpT, hp, d, hdS, hpd⟩ :
      ∃ p ∉ T, Nat.Prime p ∧ ∃ d ∈ S', p ∣ (x - m).natAbs + d :=
    hN _ (Int.ofNat_le.mp (hx.trans_eq hx0))
  refine ⟨p, hpT, hp, d - m, mem_image_of_mem _ hdS, ?_⟩
  rwa [← Int.natCast_dvd_natCast, Int.natCast_add,
    ← hx0, ← add_sub_right_comm, Int.add_sub_assoc] at hpd

/-- Final solution -/
theorem final_solution {S : Finset ℤ} (hS : #S = 9) :
    ∃ N, ∀ x ≥ N, ∃ p : ℕ, Nat.Prime p ∧ p > 20 ∧ ∃ d ∈ S, (p : ℤ) ∣ x + d := by
  ---- Apply `general_result_Int` with `T` being the set of primes `≤ 20`.
  let T : Finset ℕ := {p ∈ range 21 | Nat.Prime p}
  replace hS : #T < #S := (Nat.lt_succ_self 8).trans_eq hS.symm
  obtain ⟨N, hN⟩ : ∃ N, ∀ x ≥ N, ∃ p ∉ T, Nat.Prime p ∧ ∃ d ∈ S, (p : ℤ) ∣ x + d :=
    general_result_Int hS
  ---- Now we prove that the same `N` works.
  refine ⟨N, λ x hx ↦ ?_⟩
  obtain ⟨p, hpT, hp, hpd⟩ : ∃ p ∉ T, Nat.Prime p ∧ ∃ d ∈ S, (p : ℤ) ∣ x + d := hN x hx
  replace hpT : p > 20 := by
    rwa [mem_filter, and_iff_left hp, mem_range_succ_iff, Nat.not_le] at hpT
  exact ⟨p, hp, hpT, hpd⟩
