/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.BigInequalities.Multiset
import Mathlib.Tactic.Ring

/-!
# IMO 2010 A2

Let $R$ be a totally ordered commutative ring.
Fix some $a, b, c, d ∈ R$ such that $a + b + c + d = 6$ and $a^2 + b^2 + c^2 + d^2 = 12$.
Prove that
$$ 36 ≤ 4(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48. $$
-/

namespace IMOSL
namespace IMO2010A2

open Multiset Extra.Multiset

/-! ### Identities over commutative rings -/

section CommRing

variable [CommRing R]

theorem ring_id1 (x : R) :
    4 * x ^ 3 - x ^ 4 = 6 * x ^ 2 - 4 * x + 1 - ((x - 1) ^ 2) ^ 2 := by ring

theorem ring_id2 (S : Multiset R) :
    (S.map λ x ↦ (x - 1) ^ 2).sum = (S.map λ x ↦ x ^ 2).sum - 2 * S.sum + card S := by
  simp only [sub_sq, mul_one]
  rw [one_pow, sum_map_add, sum_map_sub, sum_map_mul_left,
    map_id', Multiset.map_const', sum_replicate, nsmul_one]

theorem ring_id3 (S : Multiset R) :
    (4 : R) * (S.map λ x ↦ x ^ 3).sum - (S.map λ x ↦ x ^ 4).sum
      = (6 * (S.map λ x ↦ x ^ 2).sum - 4 * S.sum + card S)
        - (S.map λ x ↦ ((x - 1) ^ 2) ^ 2).sum := by
  rw [← sum_map_mul_left, ← sum_map_sub, funext ring_id1, sum_map_sub,
    sum_map_add, sum_map_sub, sum_map_mul_left, sum_map_mul_left,
    map_id', Multiset.map_const', sum_replicate, nsmul_one]

end CommRing





/-! ### Solution -/

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (S : Multiset R)

/-- General lower bound -/
theorem final_solution_lower_bound :
    let B := 6 * (S.map λ x ↦ x ^ 2).sum - 4 * S.sum + card S
    let C := (S.map λ x ↦ x ^ 2).sum - 2 * S.sum + card S
    let L := (4 : R) * (S.map λ x ↦ x ^ 3).sum - (S.map λ x ↦ x ^ 4).sum
    B - C ^ 2 ≤ L := by
  rw [ring_id3, sub_le_sub_iff_left, ← ring_id2]
  refine (sq_sum_le_sum_sq λ t h ↦ ?_).trans_eq' (by rw [map_map]; rfl)
  rcases mem_map.mp h with ⟨y, -, rfl⟩; exact sq_nonneg (y - 1)

/-- General upper bound -/
theorem final_solution_upper_bound :
    let B := 6 * (S.map λ x ↦ x ^ 2).sum - 4 * S.sum + card S
    let C := (S.map λ x ↦ x ^ 2).sum - 2 * S.sum + card S
    let L := (4 : R) * (S.map λ x ↦ x ^ 3).sum - (S.map λ x ↦ x ^ 4).sum
    C ^ 2 ≤ card S • (B - L) := by
  simp only; rw [ring_id3, sub_sub_cancel, ← ring_id2]
  apply (QM_AM (S.map _)).trans_eq
  rw [card_map, map_map]; rfl

/-- Final solution -/
theorem final_solution (h : card S = 4) (h0 : S.sum = 6) (h1 : (S.map λ x ↦ x ^ 2).sum = 12) :
    let L := (4 : R) * (S.map λ x ↦ x ^ 3).sum - (S.map λ x ↦ x ^ 4).sum
    36 ≤ L ∧ L ≤ 48 := by
  have hB : 6 * (S.map λ x ↦ x ^ 2).sum - 4 * S.sum + card S = 52 := by
    rw [h, h0, h1]; norm_num
  have hC : (S.map λ x ↦ x ^ 2).sum - 2 * S.sum + card S = 4 := by
    rw [h, h0, h1]; norm_num
  constructor
  ---- Lower bound
  · apply (final_solution_lower_bound S).trans_eq'
    rw [hB, hC]; norm_num
  ---- Upper bound
  · have h2 : _ ^ 2 ≤ _ • (_ - _) := final_solution_upper_bound S
    rw [hB, hC, h, nsmul_eq_mul, Nat.cast_ofNat, sq,
      mul_le_mul_iff_of_pos_left zero_lt_four, le_sub_iff_add_le, ← le_sub_iff_add_le'] at h2
    apply h2.trans_eq; norm_num
