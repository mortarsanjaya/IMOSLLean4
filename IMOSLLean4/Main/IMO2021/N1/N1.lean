/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Factors

/-!
# IMO 2021 N1

Find all triplets $(a, b, n)$ of positive integers such that
* $a^2 + b + 3$ is cubefree; and
* $ab + 3b + 8 = n(a^2 + b + 3)$.
-/

namespace IMOSL
namespace IMO2021N1

/-! ### Formulas over `PNat` -/

theorem PNat_two_mul (k : ℕ+) : k + k = 2 * k := by
  change k + k = (1 + 1) * k; rw [add_mul, one_mul]

theorem PNat_add_sq (a b : ℕ+) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  rw [sq, add_mul, mul_add, mul_add, ← add_assoc, ← sq, ← sq,
    add_assoc (a ^ 2), mul_comm b, PNat_two_mul, mul_assoc]

theorem formula1 (a : ℕ+) : (a + 1) ^ 3 = (a + 3) * a ^ 2 + (3 * a + 1) := by
  change _ = (a + 1 + 2) * a ^ 2 + ((1 + 2) * a + 1)
  rw [add_mul, add_assoc, one_add_mul 2 a, add_assoc, ← add_assoc _ a, sq,
    ← mul_assoc 2, ← add_one_mul _ a, ← mul_add_one _ a, ← sq, mul_comm,
    ← add_mul, ← add_assoc, pow_succ, PNat_add_sq, mul_one, one_pow]

theorem formula2 (k : ℕ+) : (k + 1) ^ 2 + 2 * k + 3 = (k + 2) ^ 2 := by
  rw [PNat_add_sq, PNat_add_sq, mul_one, one_pow, add_right_comm _ 1,
    add_assoc (k ^ 2), ← add_mul, ← mul_rotate, add_assoc]; rfl

theorem min_mul_bound : ∀ k, min (3 * k) 2 ≤ 2 * k
  | 0 => Nat.le_refl 0
  | _ + 1 => min_le_of_right_le (Nat.le_add_left 2 _)





/-! ### Start of the problem -/

@[mk_iff] structure good (a b n : ℕ+) : Prop where
  cubefree : ∀ p, (a ^ 2 + b + 3).factorMultiset.count p ≤ 2
  eqn : a * b + 3 * b + 8 = n * (a ^ 2 + b + 3)



theorem good_iff_of_sol_form :
    good (k + 1) (2 * k) 2 ↔ ∀ p, (k + 2).factorMultiset.count p ≤ 1 := by
  have h0 : (k + 1) * (2 * k) + 3 * (2 * k) + 8 = 2 * (k + 2) ^ 2 := by
    rw [mul_comm, mul_add_one _ k, mul_assoc, ← mul_assoc 3, add_assoc _ (2 * k),
        ← add_mul, PNat_add_sq, ← mul_rotate, mul_add, mul_add, ← sq, ← mul_assoc]; rfl
  rw [good_iff, h0, formula2, and_iff_left rfl]
  refine forall_congr' λ p ↦ ?_
  rw [PNat.factorMultiset_pow, Multiset.count_nsmul]
  exact mul_le_mul_iff_of_pos_left Nat.two_pos (c := 1)

theorem good_imp (h : good a b n) : n = 2 ∧ b + 2 = 2 * a := by
  have h0 : (a + 3) * (a ^ 2 + b + 3) = (a + 1) ^ 3 + n * (a ^ 2 + b + 3) := by
    rw [← h.eqn, ← add_mul, add_left_comm, add_assoc, add_left_comm, mul_add, add_right_inj,
      formula1, mul_add, add_assoc, add_right_inj, add_assoc, mul_comm, mul_add]
    rfl
  have h1 : a ^ 2 + b + 3 ∣ (a + 1) ^ 3 := by
    rw [← PNat.coe_inj, PNat.mul_coe, PNat.add_coe (_ ^ 3), PNat.mul_coe] at h0
    apply Nat.sub_eq_of_eq_add at h0
    rw [PNat.dvd_iff, ← h0, ← Nat.sub_mul]
    exact Nat.dvd_mul_left _ _
  replace h1 : a ^ 2 + b + 3 ∣ (a + 1) ^ 2 := by
    rw [← PNat.factorMultiset_le_iff, Multiset.le_iff_count] at h1 ⊢
    intro p; specialize h1 p
    rw [PNat.factorMultiset_pow, Multiset.count_nsmul] at h1 ⊢
    exact (le_min_iff.mpr ⟨h1, h.cubefree p⟩).trans (min_mul_bound _)
  replace h1 : (a + 1) ^ 2  = a ^ 2 + b + 3 := by
    rcases h1 with ⟨t, h1⟩
    rw [← mul_one (a ^ 2 + b + 3), h1, mul_right_inj, ← PNat.le_one_iff]
    refine PNat.lt_add_one_iff.mp (lt_of_not_ge λ h2 ↦ h1.not_lt ?_)
    apply (mul_le_mul_left' h2 _).trans_lt' ?_
    ---- Prove the bound `(a + 1)^2 < 2(a^2 + b + 3)`
    rw [add_right_comm, add_mul, mul_add, mul_one, sq, mul_add_one _ a, add_one_mul a]
    apply (PNat.lt_add_right _ _).trans'
    rw [sq, add_assoc, add_assoc, add_lt_add_iff_left, ← add_assoc, add_left_comm]
    obtain (rfl | h3) : 1 = a ∨ 2 ≤ a := le_iff_eq_or_lt.mp a.one_le
    · exact PNat.lt_add_right 3 4
    · refine add_lt_add_of_le_of_lt ?_ (PNat.lt_add_right 1 5)
      rw [PNat_two_mul]; exact mul_le_mul_right' h3 a
  ---- Solve for `n = 2` and `b + 2 = 2a`
  constructor
  · rw [pow_succ' (a + 1), ← h1, ← add_mul, mul_left_inj, add_assoc, add_right_inj] at h0
    exact (add_right_injective 1 h0).symm
  · rw [sq, add_one_mul a, mul_add_one a, sq, add_assoc,
      add_assoc, add_right_inj, ← add_assoc, PNat_two_mul] at h1
    exact (add_left_injective 1 h1).symm

/-- Final solution -/
theorem final_solution :
    good a b n ↔ n = 2 ∧ ∃ k : ℕ+,
      (∀ p, (k + 2).factorMultiset.count p ≤ 1) ∧ a = k + 1 ∧ b = 2 * k :=
  ⟨λ h ↦ (good_imp h).imp_right λ h0 ↦ by
    obtain (rfl | h1) := eq_or_ne a 1
    · exact h0.not_gt.elim (PNat.lt_add_left 2 b)
    · rcases PNat.exists_eq_succ_of_ne_one h1 with ⟨k, rfl⟩
      rw [mul_add_one 2 k, add_left_inj] at h0; subst h0
      refine ⟨k, λ p ↦ ?_, rfl, rfl⟩
      have h0 := h.cubefree p
      rw [formula2, PNat.factorMultiset_pow, Multiset.count_nsmul] at h0
      exact (mul_le_mul_iff_of_pos_left Nat.two_pos).mp h0,
  λ h ↦ by rcases h with ⟨rfl, k, h, rfl, rfl⟩; exact good_iff_of_sol_form.mpr h⟩
