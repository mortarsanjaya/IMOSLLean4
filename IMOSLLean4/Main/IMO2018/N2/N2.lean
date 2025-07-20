/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Ring.Int.Defs

/-!
# IMO 2018 N2

Let $n$ and $k$ be positive integers.
Consider an $k × k$ table, where each cell contains an integer $1 \pmod{n}$.
Suppose that the sum of all numbers in an arbitrary row or column is $k \pmod{n^2}$.
For each $i ≤ n$, let $R_i$ and $C_i$ be the product of
  numbers in the $i$th row and $i$th column, respectively.
Prove that
$$ \sum_{i = 1}^n R_i ≡ \sum_{i = 1}^n C_i \pmod{n^4}. $$
-/

namespace IMOSL
namespace IMO2018N2

open Finset

theorem add_modeq_mul_add_one (h : a ≡ 1 [ZMOD n]) (h0 : b ≡ 1 [ZMOD n]) :
    a + b ≡ a * b + 1 [ZMOD n ^ 2] := by
  rw [Int.modEq_iff_dvd, sq, add_comm, ← sub_sub_sub_eq, ← one_sub_mul, ← mul_one_sub]
  exact mul_dvd_mul h.dvd h0.dvd

variable [DecidableEq ι] {S : Finset ι}



section

variable {n : ℤ} {f : ι → ℤ} (h : ∀ i ∈ S, f i ≡ 1 [ZMOD n])
include h

theorem prod_one_modeq_one_mod : S.prod f ≡ 1 [ZMOD n] := by
  induction' S using Finset.induction with i S h0 h1; rfl
  rw [prod_insert h0, ← Int.mul_one 1]
  exact (h i (mem_insert_self i S)).mul (h1 λ j h2 ↦ h j (mem_insert_of_mem h2))

theorem prod_one_mod_add_card_modeq_sum_add_one :
    S.prod f + S.card ≡ S.sum f + 1 [ZMOD n ^ 2] := by
  induction' S using Finset.induction with i S h0 h1; rfl
  rw [prod_insert h0, sum_insert h0, card_insert_of_notMem h0,
    Nat.cast_succ, ← add_assoc, add_right_comm]
  have h2 (j : ι) (h2 : j ∈ S) : f j ≡ 1 [ZMOD n] := h j (mem_insert_of_mem h2)
  have h3 := add_modeq_mul_add_one (h i (mem_insert_self i S)) (prod_one_modeq_one_mod h2)
  refine (h3.symm.add_right _).trans ?_
  rw [add_assoc, add_assoc]
  exact (h1 h2).add_left _

theorem prod_one_mod_modeq_one_mod_sq (h0 : S.sum f ≡ S.card [ZMOD n ^ 2]) :
    S.prod f ≡ 1 [ZMOD n ^ 2] := by
  apply prod_one_mod_add_card_modeq_sum_add_one at h
  rw [Int.add_comm _ 1] at h
  exact (h0.add_right_cancel h.symm).symm

end



/-- Final solution -/
theorem final_solution {n : ℤ} {f : ι → ι → ℤ} (h : ∀ i ∈ S, ∀ j ∈ S, f i j ≡ 1 [ZMOD n])
    (h0 : ∀ i ∈ S, ∑ j ∈ S, f i j ≡ S.card [ZMOD n ^ 2])
    (h1 : ∀ j ∈ S, ∑ i ∈ S, f i j ≡ S.card [ZMOD n ^ 2]) :
    (S.sum λ i ↦ ∏ j ∈ S, f i j) ≡ (S.sum λ j ↦ ∏ i ∈ S, f i j) [ZMOD n ^ 4] := by
  change _ ≡ _ [ZMOD n ^ (2 * 2)]; rw [pow_mul]
  refine ((prod_one_mod_add_card_modeq_sum_add_one ?_).symm.trans ?_).add_right_cancel' 1
  · exact λ i h2 ↦ prod_one_mod_modeq_one_mod_sq (h i h2) (h0 i h2)
  · rw [prod_comm]; apply prod_one_mod_add_card_modeq_sum_add_one
    exact λ j h2 ↦ prod_one_mod_modeq_one_mod_sq (h · · j h2) (h1 j h2)
