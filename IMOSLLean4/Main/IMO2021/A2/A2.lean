/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Defs

/-!
# IMO 2021 A2

For any positive integer $n$, prove that
$$ 4 \sum_{i = 1}^n \sum_{j = 1}^n \left\lfloor \frac{ij}{n + 1} \right\rfloor
  ≥ n^2 (n - 1). $$
Determine the equality cases.
-/

namespace IMOSL
namespace IMO2021A2

open Finset

/-! ### Extra lemmas -/

/-- TODO: Get this to mathlib, or delete it onces it gets to mathlib -/
lemma mod_add_mod_eq_of_dvd_add_of_not_dvd {a b c : ℕ} (h : c ∣ a + b) (ha : ¬c ∣ a) :
    c = a % c + b % c := by
  have h0 : 0 < a % c + b % c := Nat.add_pos_left (Nat.emod_pos_of_not_dvd ha) _
  have h1 : a % c + b % c < c * 2 := by
    have h1 : 0 < c := by
      refine Nat.pos_of_ne_zero λ h1 ↦ ha ?_
      rw [h1, Nat.zero_dvd] at h ⊢
      exact Nat.eq_zero_of_add_eq_zero_right h
    rw [Nat.mul_two]; exact Nat.add_lt_add (a.mod_lt h1) (b.mod_lt h1)
  obtain ⟨k, h2⟩ : c ∣ a % c + b % c := by
    rwa [Nat.dvd_iff_mod_eq_zero, ← Nat.add_mod, ← Nat.dvd_iff_mod_eq_zero]
  replace h0 : 0 < k := Nat.pos_of_mul_pos_left (h0.trans_eq h2)
  replace h1 : k < 2 := Nat.lt_of_mul_lt_mul_left (h2.symm.trans_lt h1)
  obtain rfl : k = 1 := Nat.le_antisymm (Nat.le_of_lt_succ h1) h0
  rw [h2, c.mul_one]

lemma add_mod_of_dvd (h : c ∣ a + b) : a % c + b % c = if c ∣ a then 0 else c := by
  split_ifs with h0
  · rw [Nat.mod_eq_zero_of_dvd h0, Nat.zero_add, ← Nat.dvd_iff_mod_eq_zero]
    exact (Nat.dvd_add_iff_right h0).mpr h
  · exact (mod_add_mod_eq_of_dvd_add_of_not_dvd h h0).symm

lemma add_div_of_add_eq_mul (h : 0 < c) (h0 : a + b = c * n) :
    n = a / c + b / c + if c ∣ a then 0 else 1 := by
  rw [← Nat.mul_right_inj h.ne.symm, ← h0, Nat.mul_add, Nat.mul_add, mul_ite, c.mul_zero,
    c.mul_one, ← add_mod_of_dvd ⟨n, h0⟩, Nat.add_add_add_comm, a.div_add_mod, b.div_add_mod]

lemma succ_prime_iff_not_dvd_lt_mul {n : ℕ} (h : 0 < n) :
    (n + 1).Prime ↔ ∀ i < n, ∀ j < n, ¬n + 1 ∣ (i + 1) * (j + 1) := by
  refine ⟨λ h0 i hi j hj ↦ ?_, λ h0 ↦ by_contra λ h1 ↦ ?_⟩
  ---- `→` direction
  · have X (k) (hk : k < n) : ¬n + 1 ∣ k + 1 :=
      Nat.not_dvd_of_pos_of_lt k.succ_pos (Nat.succ_lt_succ hk)
    rw [h0.dvd_mul, not_or]; exact ⟨X i hi, X j hj⟩
  ---- `←` direction
  · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero h.ne.symm
    obtain ⟨i, h2⟩ : ∃ i, (n + 2).minFac = i + 1 :=
      Nat.exists_eq_succ_of_ne_zero (n + 2).minFac_pos.ne.symm
    replace h1 : i < n + 1 := by
      rw [← Nat.add_lt_add_iff_right (k := 1), ← h2]
      exact (Nat.not_prime_iff_minFac_lt (Nat.succ_le_succ h)).mp h1
    obtain ⟨j, h3⟩ : ∃ j, (n + 2) / (n + 2).minFac = j + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero (Nat.div_pos ?_ ?_).ne.symm
      exacts [(Nat.minFac_le (n + 1).succ_pos), (n + 2).minFac_pos]
    replace h : j < n + 1 := by
      rw [← Nat.add_lt_add_iff_right (k := 1), ← h3]
      apply Nat.div_lt_self (n + 1).succ_pos
      rw [h2, Nat.succ_lt_succ_iff, Nat.pos_iff_ne_zero]
      rintro rfl; rw [Nat.minFac_eq_one_iff, Nat.succ_inj] at h2
      exact h1.ne.symm h2
    refine h0 i h1 j h (dvd_of_eq ?_)
    rw [← h2, ← h3, Nat.mul_div_cancel' (n + 2).minFac_dvd]





/-! ### Start of the problem -/

/-- The left hand side, `abbrev`ed for convenience purpose -/
abbrev targetSum (n : ℕ) := 4 * ∑ i ∈ range n, ∑ j ∈ range n, (i + 1) * (j + 1) / (n + 1)

theorem main_claim (i) (h : j ≤ n) :
    (i + 1) * (j + 1) / (n + 2) + (i + 1) * (n - j + 1) / (n + 2)
      = i + if n + 2 ∣ (i + 1) * (j + 1) then 1 else 0 := by
  apply Nat.add_right_cancel (m := if n + 2 ∣ (i + 1) * (j + 1) then 0 else 1)
  have h0 : (i + 1) * (j + 1) + (i + 1) * (n - j + 1) = (n + 2) * (i + 1) := by
    rw [← Nat.mul_add, Nat.add_add_add_comm, Nat.add_sub_cancel' h, Nat.mul_comm]
  rw [← add_div_of_add_eq_mul (n + 1).succ_pos h0, i.add_assoc, ite_add_ite, ite_self]

theorem targetSum_formula (n) :
    targetSum (n + 1) = (n + 1) ^ 2 * n +
      2 * ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
        if n + 2 ∣ (i + 1) * (j + 1) then 1 else 0 := by
  calc
    _ = 2 * (2 * ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), (i + 1) * (j + 1) / (n + 2)) :=
      Nat.mul_assoc 2 2 _
    _ = 2 * ((∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), (i + 1) * (j + 1) / (n + 2)) +
          ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), (i + 1) * (n - j + 1) / (n + 2)) := by
      apply congrArg (2 * ·)
      rw [Nat.two_mul, Nat.add_right_inj]
      exact sum_congr rfl λ i _ ↦ (sum_flip λ j ↦ (i + 1) * (j + 1) / (n + 2)).symm
    _ = 2 * ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
          (i + if n + 2 ∣ (i + 1) * (j + 1) then 1 else 0) := by
      simp_rw [← sum_add_distrib]
      refine congrArg (2 * ·) (sum_congr rfl λ i _ ↦ sum_congr rfl λ j hj ↦ ?_)
      rw [mem_range, Nat.lt_succ_iff] at hj
      exact main_claim i hj
    _ = (n + 1) ^ 2 * n + _ := ?_
  ---- Remove the residue term first
  simp_rw [sum_add_distrib]; rw [Nat.mul_add, Nat.add_left_inj]
  ---- Now continue the calculation with target `(n + 1)^2 n`
  calc
    _ = 2 * ∑ i ∈ range (n + 1), (n + 1) * i := by
      simp only [sum_const, card_range]; rfl
    _ = ∑ i ∈ range (n + 1), ((n + 1) * (n - i) + (n + 1) * i) := by
      rw [Nat.two_mul, sum_add_distrib, sum_flip]
    _ = ∑ i ∈ range (n + 1), (n + 1) * n := by
      refine sum_congr rfl λ i hi ↦ ?_
      rw [mem_range, Nat.lt_succ_iff] at hi
      rw [← Nat.mul_add, Nat.sub_add_cancel hi]
    _ = (n + 1) ^ 2 * n := by
      rw [sum_const, card_range, sq, Nat.mul_assoc]; rfl

theorem main_ineq (n) : (n + 1) ^ 2 * n ≤ targetSum (n + 1) :=
  Nat.le_of_add_right_le (targetSum_formula n).ge

theorem eq_case (n) : targetSum (n + 1) = (n + 1) ^ 2 * n ↔ (n + 2).Prime := by
  rw [targetSum_formula, add_eq_left, Nat.mul_eq_zero,
    or_iff_right (Nat.succ_ne_zero 1), sum_eq_zero_iff]
  simp only [mem_range, sum_eq_zero_iff, ite_eq_right_iff, one_ne_zero, imp_false]
  exact (succ_prime_iff_not_dvd_lt_mul n.succ_pos).symm

/-- Final solution, inequality -/
theorem final_solution_ineq (hn : n ≠ 0) : n ^ 2 * (n - 1) ≤ targetSum n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n.pred, (Nat.succ_pred hn).symm⟩
  exact main_ineq k

/-- Final solution -/
theorem final_solution (hn : n ≠ 0) : targetSum n = n ^ 2 * (n - 1) ↔ (n + 1).Prime := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n.pred, (Nat.succ_pred hn).symm⟩
  exact eq_case k
