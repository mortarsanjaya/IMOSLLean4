/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Analysis.MeanInequalities
import IMOSLLean4.Extra.BigInequalities.Multiset
import Mathlib.Data.Multiset.Fintype

/-!
# IMO 2020 A4 (P2)

Let $a, b, c, d ∈ ℝ$ with $a ≥ b ≥ c ≥ d > 0$ and $a + b + c + d = 1$.
Prove that $$ (a + 2b + 3c + 4d) a^a b^b c^c d^d < 1. $$
-/

namespace IMOSL
namespace IMO2020A4

open Multiset Extra.Multiset

theorem Multiset_weighted_AM_GM {S : Multiset NNReal} (hS : S.sum = 1) :
    (S.map λ x ↦ x ^ x.1).prod ≤ (S.map (· ^ 2)).sum := by
  rw [← S.map_univ, ← S.map_univ]; simp only [sq]
  apply NNReal.geom_mean_le_arith_mean_weighted
  rw [← S.sum_eq_sum_coe, hS]

theorem NNReal_rpow_sum (a : NNReal) (S : Finset ι) (f : ι → NNReal) :
    a ^ ((∑ x ∈ S, f x : NNReal) : ℝ) = ∏ x ∈ S, a ^ (f x : ℝ) := by
  rw [← NNReal.coe_inj, NNReal.coe_rpow, NNReal.coe_sum, NNReal.coe_prod,
    Real.rpow_sum_of_nonneg NNReal.zero_le_coe (λ _ _ ↦ NNReal.zero_le_coe)]; rfl

/-- General inequality -/
theorem general_ineq
    (hS : 1 < card S) (hS0 : ∀ x ∈ S, 0 < x) (hSa : ∀ x ∈ S, x ≤ a) (h : a + S.sum = 1) :
    (a + 3 * S.sum) * ((a ::ₘ S).map λ x ↦ (x : NNReal) ^ (x : ℝ)).prod < 1 := by
  obtain h0 | h0 : 2 * a < 1 ∨ 1 ≤ 2 * a := lt_or_ge _ _
  ---- Case 1: `a < 1/2`
  · have h1 : ((a ::ₘ S).map λ x ↦ (x : NNReal) ^ (x : ℝ)).prod ≤ a := calc
      _ = ∏ x : a ::ₘ S, (x : NNReal) ^ (x : ℝ) := by rw [← map_univ]; rfl
      _ ≤ ∏ x : a ::ₘ S, a ^ (x : ℝ) := by
        refine Finset.prod_le_prod' λ i _ ↦ NNReal.rpow_le_rpow ?_ NNReal.zero_le_coe
        obtain h2 | h2 : i.1 = a ∨ i.1 ∈ S := mem_cons.mp coe_mem
        exacts [h2.le, hSa _ h2]
      _ = a := by rw [← NNReal_rpow_sum, Finset.sum, map_univ_coe,
        sum_cons, h, NNReal.coe_one, NNReal.rpow_one]
    apply (mul_le_mul_left' h1 _).trans_lt
    -- Remains to show that `(a + 3 Σ_S) a = 1`
    rw [← two_add_one_eq_three, add_one_mul, add_left_comm, h,
      add_one_mul, mul_right_comm, ← h, add_comm, add_lt_add_iff_left]
    refine (mul_lt_iff_lt_one_left ?_).mpr h0
    rw [two_mul, ← h, add_lt_add_iff_left] at h0
    exact pos_of_gt h0
  ---- Case 2: `a ≥ 1/2`
  · apply (mul_le_mul_left' (Multiset_weighted_AM_GM ((sum_cons _ _).trans h)) _).trans_lt
    rw [← two_add_one_eq_three, add_one_mul, add_left_comm, h, map_cons, sum_cons]
    apply (mul_lt_mul_of_pos_left (add_lt_add_left (sq_sum_lt_sum_sq hS0 hS) _)
      (add_pos_of_nonneg_of_pos (zero_le _) one_pos)).trans_le
    rw [← add_le_add_iff_right ((2 * S.sum + 1) * (2 * a * S.sum)), ← mul_add, ← add_sq',
      h, one_pow, mul_one, add_comm, add_le_add_iff_left, mul_right_comm, mul_left_comm]
    apply le_mul_of_one_le_right'
    rw [one_add_mul, ← h, add_le_add_iff_left, mul_right_comm]
    exact le_mul_of_one_le_left' h0

/-- Final solution -/
theorem final_solution {a b c d : NNReal}
    (hd : 0 < d) (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a) (h : a + b + c + d = 1) :
    (a + 2 * b + 3 * c + 4 * d) *
      (a ^ (a : ℝ) * b ^ (b : ℝ) * c ^ (c : ℝ) * d ^ (d : ℝ)) < 1 := by
  have h0 : a + 2 * b + 3 * c + 4 * d ≤ a + 3 * (b ::ₘ c ::ₘ {d}).sum := by
    rw [add_assoc, add_assoc, add_le_add_iff_left, ← three_add_one_eq_four,
      add_one_mul, ← add_assoc (3 * c), ← add_rotate', sum_cons, sum_cons,
      sum_singleton, mul_add, ← mul_add, ← add_assoc, add_le_add_iff_right,
      ← two_add_one_eq_three, add_one_mul, add_comm, add_le_add_iff_left]
    exact hdc.trans hcb
  have h1 : (a ^ (a : ℝ) * b ^ (b : ℝ) * c ^ (c : ℝ) * d ^ (d : ℝ))
      = ((a ::ₘ b ::ₘ c ::ₘ {d}).map λ x ↦ (x : NNReal) ^ (x : ℝ)).prod := by
    simp only [map_cons, prod_cons, mul_assoc]; rw [map_singleton, prod_singleton]
  apply (mul_le_mul' h0 h1.le).trans_lt
  clear h0 h1; apply general_ineq
  · exact Nat.lt_add_of_pos_left Nat.two_pos
  · have hc : 0 < c := hd.trans_le hdc
    rw [forall_mem_cons, forall_mem_cons]
    exact ⟨hc.trans_le hcb, hc, λ x h0 ↦ hd.trans_eq (mem_singleton.mp h0).symm⟩
  · have hca : c ≤ a := hcb.trans hba
    rw [forall_mem_cons, forall_mem_cons]
    exact ⟨hba, hca, λ x h0 ↦ (mem_singleton.mp h0).trans_le (hdc.trans hca)⟩
  · rw [sum_cons, sum_cons, sum_singleton, ← add_assoc, ← add_assoc, h]
