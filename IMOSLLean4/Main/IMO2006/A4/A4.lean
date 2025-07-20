/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# IMO 2006 A4

Let $F$ be a totally ordered field and $a_1, a_2, …, a_n ∈ F$ be positive.
Prove the inequality
$$ \sum_{i < j} \frac{a_i a_j}{a_i + a_j}
  ≤ \frac{n}{2(a_1 + a_2 + … + a_n)} \sum_{i < j} a_i a_j. $$
-/

namespace IMOSL
namespace IMO2006A4

open Finset

/-! ### Summation identities -/

theorem sum_offDiag_eq' [AddCommMonoid M] [DecidableEq ι] (a : ι × ι → M) (S : Finset ι) :
    S.sum (λ i ↦ a (i, i)) + S.offDiag.sum a = (S ×ˢ S).sum a := by
  rw [← S.sum_diag, ← sum_disjUnion S.disjoint_diag_offDiag,
    ← diag_union_offDiag, disjUnion_eq_union]

theorem sum_offDiag_eq [AddCommGroup G] [DecidableEq ι] (a : ι × ι → G) (S : Finset ι) :
    S.offDiag.sum a = (S ×ˢ S).sum a - S.sum (λ i ↦ a (i, i)) :=
  eq_sub_of_add_eq' (sum_offDiag_eq' a S)

section

variable [AddCommMonoid M] [LinearOrder ι] (S : Finset ι)

theorem orderedPair_sum_eq_offDiag (a : ι × ι → M) :
    ((S ×ˢ S).filter λ p ↦ p.1 < p.2).sum a + ((S ×ˢ S).filter λ p ↦ p.2 < p.1).sum a
      = S.offDiag.sum a := by
  have h : Disjoint ((S ×ˢ S).filter λ p ↦ p.1 < p.2) ((S ×ˢ S).filter λ p ↦ p.2 < p.1) :=
    disjoint_left.mpr λ p h h0 ↦ (mem_filter.mp h).2.asymm (mem_filter.mp h0).2
  rw [← sum_disjUnion h]; refine sum_congr ?_ λ _ _ ↦ rfl
  ---- Now show that the union of the two sets is indeed the off-diagonal set
  rw [disjUnion_eq_union, ← filter_or]
  simp only [lt_or_lt_iff_ne]; rfl

theorem orderedPair_symm_sum {a : ι × ι → M} (ha : ∀ p, a p.swap = a p) :
    ((S ×ˢ S).filter λ p ↦ p.1 < p.2).sum a = ((S ×ˢ S).filter λ p ↦ p.2 < p.1).sum a := by
  refine sum_bijective Prod.swap Prod.swap_bijective (λ p ↦ ?_) (λ p _ ↦ (ha p).symm)
  rw [mem_filter, mem_filter, mem_product, mem_product]
  exact and_congr_left' and_comm

theorem orderedPair_sum_eq_offDiag_of_symm {a : ι × ι → M} (ha : ∀ p, a p.swap = a p) :
    2 • ((S ×ˢ S).filter λ p ↦ p.1 < p.2).sum a = S.offDiag.sum a := by
  rw [two_nsmul, ← orderedPair_sum_eq_offDiag, orderedPair_symm_sum S ha]

end





/-! ### Field identities -/

section

variable [Field F]

theorem field_id1 (x y : F) : 2 ^ 2 * (x * y / (x + y)) = x + y - (x - y) ^ 2 / (x + y) := by
  by_cases h : x + y = 0
  · rw [h, div_zero, div_zero, sub_zero, mul_zero]
  · rw [← mul_div_assoc, div_eq_iff h, sub_mul, ← sq, div_mul_cancel₀ _ h,
      add_sq', sub_sq', add_sub_sub_cancel, mul_assoc, ← add_mul, ← two_mul, sq]

variable [DecidableEq ι] (a : ι → F) (S : Finset ι)

theorem field_id2 : S.offDiag.sum (λ p ↦ a p.1 + a p.2) = 2 * ((S.card - 1) * S.sum a) := by
  rw [sum_add_distrib, sum_offDiag_eq, sum_offDiag_eq, sum_product, sum_product]
  simp only [sum_const]; rw [sum_nsmul, ← two_mul, nsmul_eq_mul, sub_one_mul]

theorem field_id3 :
    2 ^ 2 * S.offDiag.sum (λ p ↦ a p.1 * a p.2 / (a p.1 + a p.2))
      = 2 * ((S.card - 1) * S.sum a)
        - S.offDiag.sum (λ p ↦ (a p.1 - a p.2) ^ 2 / (a p.1 + a p.2)) := by
  rw [mul_sum]; simp only [field_id1]
  rw [sum_sub_distrib, field_id2]

theorem field_id4 :
    S.offDiag.sum (λ p ↦ (a p.1 - a p.2) ^ 2)
      = 2 * (S.card • S.sum λ i ↦ a i ^ 2) - 2 * S.sum a ^ 2 := by
  rw [sum_offDiag_eq, sum_product]
  simp only [sub_self, sub_sq', sum_sub_distrib, sum_add_distrib, sum_const]
  rw [zero_pow (Nat.succ_ne_zero 1), nsmul_zero, sub_zero, sum_nsmul, ← two_mul]
  simp only [← mul_sum]; rw [← sum_mul, ← mul_sum, mul_assoc, sq]

theorem field_id5 :
    S.offDiag.sum (λ p ↦ a p.1 * a p.2) = S.sum a ^ 2 - S.sum (λ i ↦ a i ^ 2) := by
  rw [sum_offDiag_eq, sum_product]
  simp only [← mul_sum, sq]; rw [sum_mul]

end





/-! ### Final solution -/

/-- Final solution, unordered version -/
theorem final_solution_unordered [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [DecidableEq ι] (a : ι → F) {S : Finset ι} (hS : ∀ i ∈ S, 0 < a i) :
    S.offDiag.sum (λ p ↦ a p.1 * a p.2 / (a p.1 + a p.2))
      ≤ S.card • S.offDiag.sum (λ p ↦ a p.1 * a p.2) / (2 * S.sum a) := by
  ---- First resolve the case where `S` is empty
  obtain (rfl | hS0) : S = ∅ ∨ S.Nonempty := eq_empty_or_nonempty S
  · rw [offDiag_empty, sum_empty, card_empty, zero_nsmul, zero_div]
  ---- Next manipulate and reduce to `(a_i - a_j)^2 ≤ (a_i - a_j)^2 S/(a_i + a_j)`
  have h : (0 : F) < 2 := two_pos
  rw [le_div_iff₀' (mul_pos two_pos (sum_pos hS hS0)), ← mul_le_mul_left h,
    mul_right_comm, ← mul_assoc, ← mul_assoc, ← sq, field_id3, sub_one_mul,
    mul_sub, sub_sub, sub_mul, mul_assoc, mul_assoc, ← sq, ← nsmul_eq_mul,
    field_id5, nsmul_sub, mul_sub, sub_le_sub_iff_left, add_mul,
    ← sub_le_iff_le_add', mul_assoc, ← sq, ← field_id4, sum_mul]
  refine sum_le_sum λ (i, j) h0 ↦ ?_
  ---- Prove `(a_i - a_j)^2 ≤ (a_i - a_j)^2 S/(a_i + a_j)` for `i ≠ j`
  rw [mem_offDiag] at h0; rcases h0 with ⟨hi, hj, h⟩
  rw [← mul_div_right_comm, le_div_iff₀ (add_pos (hS i hi) (hS j hj))]
  exact mul_le_mul_of_nonneg_left (add_le_sum (λ k hk ↦ (hS k hk).le) hi hj h) (sq_nonneg _)

/-- Final solution -/
theorem final_solution [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [LinearOrder ι] (a : ι → F) {S : Finset ι} (hS : ∀ i ∈ S, 0 < a i) :
    let T := (S ×ˢ S).filter λ p ↦ p.1 < p.2
    T.sum (λ p ↦ a p.1 * a p.2 / (a p.1 + a p.2))
      ≤ S.card • T.sum (λ p ↦ a p.1 * a p.2) / (2 * S.sum a) := by
  apply le_of_nsmul_le_nsmul_right (Nat.succ_ne_zero 1)
  have h (i j) : a i * a j / (a i + a j) = a j * a i / (a j + a i) := by
    rw [add_comm, mul_comm]
  have h0 (i j) : a i * a j = a j * a i := mul_comm _ _
  rw [orderedPair_sum_eq_offDiag_of_symm _ (λ _ ↦ h _ _), nsmul_eq_mul,
    nsmul_eq_mul, ← mul_div_assoc, mul_left_comm, ← nsmul_eq_mul,
    ← nsmul_eq_mul, orderedPair_sum_eq_offDiag_of_symm _ (λ _ ↦ h0 _ _)]
  exact final_solution_unordered a hS
