/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# IMO 2015 N3

Let $m$ and $n > 1$ be positive integers such that $k ∣ m$ whenever $n ≤ k < 2n$.
Prove that $L - 1$ is not a power of $2$, where
$$ L = \prod_{k = n}^{2n - 1} \left(\frac{m}{k} + 1\right). $$
-/

namespace IMOSL
namespace IMO2015N3

open Finset

lemma div_pos_of_dvd (hm : 0 < m) (hk : k ∣ m) : 0 < m / k :=
  Nat.pos_of_mul_pos_right (hm.trans_eq (Nat.div_mul_cancel hk).symm)

lemma clog_base_mul (hb : 1 < b) (hn : 0 < n) : b.clog (b * n) = b.clog n + 1 := by
  refine (Nat.clog_of_two_le hb (Nat.mul_le_mul hb hn)).trans (congrArg (b.clog · + 1) ?_)
  have hb' : 0 < b := Nat.zero_lt_of_lt hb
  rw [Nat.add_sub_assoc hb.le, Nat.mul_add_div hb', Nat.add_eq_left, Nat.div_eq_zero_iff]
  exact Or.inr (Nat.sub_one_lt_of_lt hb)

lemma two_pow_clog_mem_Ico (hn : 0 < n) : 2 ^ Nat.clog 2 n ∈ Ico n (2 * n) := by
  have X : 1 < 2 := Nat.one_lt_two
  refine mem_Ico.mpr ⟨Nat.le_pow_clog X n, ?_⟩
  rw [Nat.pow_lt_iff_lt_clog X, clog_base_mul X hn, Nat.lt_succ_iff]

lemma prod_mod_ne_one [DecidableEq ι] {I : Finset ι}
    {f : ι → ℕ} (h : ∃ i₀ ∈ I, ∀ i ∈ I, n ∣ f i ↔ i ≠ i₀) :
    (∏ i ∈ I, (f i + 1)) % n ≠ 1 % n := by
  rcases h with ⟨i₀, hi₀, h⟩
  obtain ⟨I, hi₀', rfl⟩ : ∃ I' : Finset ι, i₀ ∉ I' ∧ insert i₀ I' = I :=
    ⟨I.erase i₀, I.notMem_erase i₀, insert_erase hi₀⟩
  replace hi₀ : ¬n ∣ f i₀ := (not_congr (h i₀ hi₀)).mpr (· rfl)
  replace h (i) (hi : i ∈ I) : (f i + 1) % n = 1 % n := by
    obtain ⟨k, h0⟩ := (h i (mem_insert_of_mem hi)).mpr (ne_of_mem_of_not_mem hi hi₀')
    rw [h0, Nat.add_comm, Nat.add_mul_mod_self_left]
  rw [prod_nat_mod, prod_insert hi₀', prod_congr rfl h, ← Nat.mul_mod_mod,
    ← prod_nat_mod, prod_const_one, ← Nat.mul_mod, Nat.mul_one]
  intro h0; replace h0 : (f i₀ + 1 - 1) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq h0
  rw [Nat.add_sub_cancel, ← Nat.dvd_iff_mod_eq_zero] at h0
  exact hi₀ h0

lemma main_lemma (hm : 0 < m) (hn : 0 < n) (h : ∀ k ∈ Ico n (2 * n), k ∣ m) :
    ∃ t, ∀ k ∈ Ico n (2 * n), 2 ^ t ∣ m / k ↔ k ≠ 2 ^ Nat.clog 2 n := by
  refine ⟨m.factorization 2 - Nat.clog 2 n + 1, λ k hk ↦ ?_⟩
  have X {k x} (hx : 0 < x) : 2 ^ k ∣ x ↔ k ≤ x.factorization 2 :=
    Nat.prime_two.pow_dvd_iff_le_factorization hx.ne.symm
  have X0 : Nat.clog 2 n ≤ m.factorization 2 := (X hm).mp (h _ (two_pow_clog_mem_Ico hn))
  specialize h k hk
  have hk0 : 0 < k := Nat.pos_of_dvd_of_pos h hm
  rw [iff_not_comm, X (div_pos_of_dvd hm h), Nat.factorization_div h, Nat.not_le,
    Nat.lt_succ_iff, Finsupp.coe_tsub, Pi.sub_apply, Nat.sub_le_sub_iff_left X0, ← X hk0]
  refine ⟨λ h0 ↦ dvd_of_eq h0.symm, λ h0 ↦ (Nat.eq_of_dvd_of_lt_two_mul hk0.ne.symm h0 ?_)⟩
  exact (mem_Ico.mp hk).2.trans_le (Nat.mul_le_mul_left 2 (Nat.le_pow_clog Nat.one_lt_two _))

/-- Final solution -/
theorem final_solution (hm : 0 < m) (hn : 1 < n) (h : ∀ k ∈ Ico n (2 * n), k ∣ m) :
    ∀ N, ∏ k ∈ Ico n (2 * n), (m / k + 1) ≠ 2 ^ N + 1 := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  obtain ⟨t, ht⟩ := main_lemma hm hn0 h
  intro N hN; obtain h0 | h0 : t ≤ N ∨ N < t := le_or_gt t N
  ---- Case 1: `t ≤ N`
  · apply prod_mod_ne_one ⟨2 ^ Nat.clog 2 n, two_pow_clog_mem_Ico hn0, ht⟩
    obtain ⟨c, rfl⟩ : ∃ c, N = t + c := Nat.exists_eq_add_of_le h0
    rw [hN, Nat.pow_add, Nat.add_comm, Nat.add_mul_mod_self_left]
  ---- Case 2: `N < t`
  · revert hN; apply Nat.ne_of_gt
    apply (Nat.add_lt_add_right (Nat.pow_lt_pow_right Nat.one_lt_two h0) 1).trans_le
    obtain ⟨k₀, hk₀, hk₀0⟩ : ∃ k ∈ Ico n (2 * n), k ≠ 2 ^ Nat.clog 2 n := by
      apply exists_mem_ne; rwa [Nat.card_Ico, Nat.two_mul, Nat.add_sub_cancel]
    replace hk₀0 : 2 ^ t + 1 ≤ m / k₀ + 1 := by
      refine Nat.add_le_add_right (Nat.le_of_dvd ?_ ((ht _ hk₀).mpr hk₀0)) 1
      exact div_pos_of_dvd hm (h _ hk₀)
    rw [← prod_erase_mul _ _ hk₀]
    exact hk₀0.trans (Nat.le_mul_of_pos_left _ (prod_pos λ _ _ ↦ Nat.succ_pos _))
