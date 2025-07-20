/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
# IMO 2019 A2

Let $R$ be a totally ordered ring and $x_1, x_2, …, x_n ∈ R$ be elements with
$$ x_1 + x_2 + … + x_n = 0. $$
Let $a, b ∈ R$ such that $b ≤ x_i ≤ a$ for all $i ≤ n$.
Show that $$ nab + \sum_{i = 1}^n x_i^2 ≤ 0. $$
-/

namespace IMOSL
namespace IMO2019A2

open Multiset

theorem final_solution [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] {M : Multiset R} (hM : M.sum = 0)
    (ha : ∀ x ∈ M, x ≤ a) (hb : ∀ x ∈ M, b ≤ x) :
    card M • (a * b) + (M.map λ x ↦ x ^ 2).sum ≤ 0 := by
  obtain h | h : card M = 0 ∨ card M ≠ 0 := Decidable.eq_or_ne (card M) 0
  · rw [h, zero_nsmul, zero_add, card_eq_zero.mp h, Multiset.map_zero, sum_zero]
  ---- Now focus on case `M` non-empty
  have ha0 : 0 ≤ a := by
    apply le_of_nsmul_le_nsmul_right h
    rw [nsmul_zero, ← hM]
    exact sum_le_card_nsmul M a ha
  have hb0 : b ≤ 0 := by
    apply le_of_nsmul_le_nsmul_right h
    rw [nsmul_zero, ← hM]
    exact card_nsmul_le_sum hb
  let N := M.filter λ x ↦ x ≤ 0
  let P := M.filter λ x ↦ ¬x ≤ 0
  have h0 : (N.map λ x ↦ x ^ 2).sum ≤ (N.map λ x ↦ x * b).sum :=
    sum_map_le_sum_map _ _ λ x hx ↦ let hx := mem_filter.mp hx;
      (sq x).trans_le (mul_le_mul_of_nonpos_left (hb x hx.1) hx.2)
  have h1 : (P.map λ x ↦ x ^ 2).sum ≤ (P.map λ x ↦ a * x).sum :=
    sum_map_le_sum_map _ _ λ x hx ↦ let hx := mem_filter.mp hx;
      (sq x).trans_le (mul_le_mul_of_nonneg_right (ha x hx.1) (le_of_not_ge hx.2))
  replace h : (M.map λ x ↦ x ^ 2).sum ≤ (N.map λ x ↦ x * b).sum + (P.map λ x ↦ a * x).sum := by
    apply (add_le_add h0 h1).trans_eq'
    rw [← sum_add, ← Multiset.map_add, filter_add_not]
  replace h0 : card N • (a * b) ≤ (N.map λ x ↦ a * x).sum := by
    rw [← sum_replicate, ← map_const']
    exact sum_map_le_sum_map _ _ λ x hx ↦
      mul_le_mul_of_nonneg_left (hb x (mem_filter.mp hx).1) ha0
  replace h1 : card P • (a * b) ≤ (P.map λ x ↦ x * b).sum := by
    rw [← sum_replicate, ← map_const']
    exact sum_map_le_sum_map _ _ λ x hx ↦
      mul_le_mul_of_nonpos_right (ha x (mem_filter.mp hx).1) hb0
  replace h0 : card M • (a * b) ≤ (N.map λ x ↦ a * x).sum + (P.map λ x ↦ x * b).sum := by
    apply (add_le_add h0 h1).trans_eq'
    rw [← add_nsmul, ← card_add, filter_add_not]
  refine (add_le_add h0 h).trans_eq ?_
  rw [add_comm (sum _), add_add_add_comm, ← sum_add, ← sum_add, ← Multiset.map_add,
    ← Multiset.map_add, add_comm P, filter_add_not, sum_map_mul_left,
    sum_map_mul_right, map_id', hM, zero_mul, mul_zero, add_zero]
