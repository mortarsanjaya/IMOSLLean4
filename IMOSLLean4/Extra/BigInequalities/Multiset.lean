/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Big inequalities over multiset

We prove some big inequalities using big operators on `Multiset`.
-/

namespace IMOSL
namespace Extra

open Multiset

namespace Multiset

variable [LinearOrderedCommSemiring R]

/-- `x_1^2 + x_2^2 + … + x_n^2 ≤ (x_1 + x_2 + … + x_n)^2` -/
theorem sq_sum_le_sum_sq {S : Multiset R} (hS : ∀ x ∈ S, 0 ≤ x) :
    (S.map λ x ↦ x ^ 2).sum ≤ S.sum ^ 2 := by
  induction' S using Multiset.induction with c S h
  · rw [Multiset.map_zero, sum_zero, zero_pow (Nat.succ_ne_zero 1)]
  · rw [forall_mem_cons] at hS
    rw [map_cons, sum_cons, sum_cons, add_sq]
    refine add_le_add (le_add_of_nonneg_right ?_) (h hS.2)
    exact mul_nonneg (mul_nonneg zero_le_two hS.1) (sum_nonneg hS.2)

/-- `sq_sum_le_sum_sq` is strict if `|S| > 1` and all its elements are positive. -/
theorem sq_sum_lt_sum_sq {S : Multiset R} (hS : ∀ x ∈ S, 0 < x) (h : 1 < card S) :
    (S.map λ x ↦ x ^ 2).sum < S.sum ^ 2 := by
  obtain ⟨a, S', rfl⟩ : ∃ a S', S = a ::ₘ S' :=
    (card_pos_iff_exists_mem.mp (Nat.zero_lt_of_lt h)).imp λ _ ↦ exists_cons_of_mem
  rw [card_cons, Nat.lt_add_left_iff_pos, card_pos_iff_exists_mem] at h
  obtain ⟨b, S, rfl⟩ : ∃ b S, S' = b ::ₘ S := h.imp λ _ ↦ exists_cons_of_mem
  rw [forall_mem_cons, forall_mem_cons] at hS
  replace h : a ^ 2 + b ^ 2 < (a + b) ^ 2 := by
    rw [add_sq', lt_add_iff_pos_right]; exact mul_pos (mul_pos two_pos hS.1) hS.2.1
  rw [map_cons, map_cons, sum_cons, sum_cons, sum_cons, sum_cons, ← add_assoc, ← add_assoc]
  have h0 (x) (h0 : x ∈ S) : 0 ≤ x := (hS.2.2 _ h0).le
  apply (add_lt_add_of_lt_of_le h (sq_sum_le_sum_sq h0)).trans_le
  rw [add_sq' (a + b), le_add_iff_nonneg_right]
  exact mul_nonneg (mul_nonneg zero_le_two (add_pos hS.1 hS.2.1).le) (sum_nonneg h0)


variable [ExistsAddOfLE R]

/-- `QM-AM inequality`: `(x_1 + x_2 + … + x_n)^2 ≤ n(x_1^2 + x_2^2 + … + x_n^2)`. -/
theorem QM_AM (S : Multiset R) : S.sum ^ 2 ≤ card S • (S.map λ x ↦ x ^ 2).sum := by
  induction' S using Multiset.induction with c S hS
  · rw [card_zero, zero_nsmul, sum_zero, zero_pow (Nat.succ_ne_zero 1)]
  · rw [map_cons, sum_cons, sum_cons, card_cons, succ_nsmul, add_sq, nsmul_add,
      add_left_comm, add_assoc, add_le_add_iff_left, add_right_comm]
    refine add_le_add ?_ hS
    rw [← sum_replicate, ← Multiset.map_const', ← sum_map_add,
      ← map_id' S, ← sum_map_mul_left, map_id']
    exact sum_map_le_sum_map _ _ λ x _ ↦ two_mul_le_add_sq c x
