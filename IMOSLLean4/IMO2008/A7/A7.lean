/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# IMO 2008 A7

Let $F$ be a totally ordered field.
1. Prove that, for any $a, b, c, d ∈ F$ positive,
$$ \frac{(a - b)(a - c)}{a + b + c} + \frac{(b - c)(b - d)}{b + c + d} +
  \frac{(c - d)(c - a)}{c + d + a} + \frac{(d - a)(d - b)}{d + a + b} ≥ 0. $$
2. Find all cases of equality.
-/

namespace IMOSL
namespace IMO2008A7

theorem group_ineq [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    {a b : G} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ≤ max a b := by
  rw [abs_sub_le_iff, le_max_iff, le_max_iff]
  exact ⟨Or.inl (sub_le_self a hb), Or.inr (sub_le_self b ha)⟩

theorem field_id [Field F] {a b c d : F} (h : a + c + b ≠ 0) (h0 : a + c + d ≠ 0) :
    2 * ((a - b) / (a + c + b) - (c - d) / (a + c + d))
      = (a - c) / (a + c + b) + (a - c) / (a + c + d)
        + 3 * (d - b) * (a + c) / ((a + c + b) * (a + c + d)) := by
  field_simp; ring



variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- A form of Cauchy-Schwarz inequality -/
theorem field_ineq1 (a b : F) (hc : 0 < c) (hd : 0 < d) :
    (a + b) ^ 2 / (c + d) ≤ a ^ 2 / c + b ^ 2 / d := by
  have hc0 : c ≠ 0 := hc.ne.symm
  have hd0 : d ≠ 0 := hd.ne.symm
  rw [div_le_iff₀ (add_pos hc hd), add_sq, add_mul, mul_add, mul_add, ← add_assoc,
    div_mul_cancel₀ _ hc0, div_mul_cancel₀ _ hd0, add_le_add_iff_right,
    add_assoc, add_le_add_iff_left, ← mul_div_right_comm, ← mul_div_right_comm,
    div_add_div _ _ hc0 hd0, mul_assoc, mul_assoc, ← sq, mul_left_comm c, ← sq,
    ← mul_pow, ← mul_pow, le_div_iff₀ (mul_pos hc hd), mul_assoc, mul_comm c,
    mul_mul_mul_comm, ← mul_assoc]
  exact two_mul_le_add_sq (a * d) (b * c)

/-- The above inequality with `a = b = 1` -/
theorem field_ineq2 {c d : F} (hc : 0 < c) (hd : 0 < d) : 4 / (c + d) ≤ c⁻¹ + d⁻¹ := by
  have h0 : (1 + 1 : F) ^ 2 = 4 := by norm_num
  have h := field_ineq1 1 1 hc hd
  rwa [one_pow, one_div, one_div, h0] at h

theorem field_ineq3 {a b c d : F} (h : 0 < a + c + b) (h0 : 0 < a + c + d) :
    4 * (a - c) ^ 2 / (2 * (a + c) + (b + d))
      + 3 * (a - c) * (d - b) * ((a + c) / ((a + c + b) * (a + c + d)))
      ≤ 2 * ((a - b) * (a - c) / (a + b + c) + (c - d) * (c - a) / (c + d + a)) := by
  rw [← neg_sub a c, mul_comm (a - b), mul_div_assoc (a - c), mul_comm (c - d), neg_mul,
    ← mul_neg, mul_div_assoc (a - c), ← mul_add, mul_left_comm, neg_div, ← sub_eq_add_neg,
    add_right_comm a b, ← add_rotate a c d, field_id h.ne.symm h0.ne.symm, mul_add (a - c)]
  refine add_le_add ?_ (le_of_eq ?_)
  · rw [div_eq_mul_inv (a - c), div_eq_mul_inv (a - c),
      ← mul_add, ← mul_assoc, ← sq, mul_comm, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ((field_ineq2 h h0).trans_eq' ?_) (sq_nonneg _)
    rw [add_add_add_comm, ← two_mul]
  · rw [mul_div_assoc, mul_comm 3, mul_assoc, mul_assoc, mul_assoc]





/-! ### Start of the problem -/

variable {a b c d : F} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
include ha hb hc hd

/-- Non-trivial estimate -/
theorem lower_bound :
    (4 * (|a - c| + |b - d|) ^ 2 - 9 * (|a - c| * |b - d|)) / (6 * ((a + c) + (b + d)))
      ≤ (a - b) * (a - c) / (a + b + c) + (b - c) * (b - d) / (b + c + d)
        + (c - d) * (c - a) / (c + d + a) + (d - a) * (d - b) / (d + a + b) := by
  have X : (6 : F) = 2 * 3 := by norm_num
  rw [X, mul_assoc, mul_comm 2, ← div_div, div_le_iff₀' zero_lt_two,
    add_assoc (_ / _ + _), add_add_add_comm (_ / _), mul_add 2]
  have hy : 0 < a + c := add_pos ha hc
  have hz : 0 < b + d := add_pos hb hd
  apply (add_le_add (field_ineq3 (add_pos hy hb) (add_pos hy hd))
    (field_ineq3 (add_pos hz hc) (add_pos hz ha))).trans'
  rw [sub_div, add_add_add_comm (4 * _ / _), sub_eq_add_neg]
  refine add_le_add ?_ ?_
  ---- `4(|ε| + |δ|)^2/(3(y + z)) ≤ 4ε^2/(2y + z) + 4δ^2/(2z + y)`
  · rw [mul_div_assoc, mul_div_assoc, mul_div_assoc, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_four
    rw [← sq_abs (a - c), ← sq_abs (b - d), add_comm c]
    replace X {u v : F} (h : 0 < u) (h0 : 0 < v) : 0 < 2 * u + v :=
      add_pos (mul_pos zero_lt_two h) h0
    refine (field_ineq1 _ _ (X hy hz) (X hz hy)).trans_eq' (congrArg₂ _ rfl ?_)
    rw [add_add_add_comm (2 * _), ← mul_add, add_comm, ← add_one_mul, two_add_one_eq_three]
  ---- `|y/((y + b)(y + d)) - z/((z + a)(z + c))| ≤ 1/(y + z)`
  · replace X : (9 : F) = 3 * 3 := by norm_num
    rw [X, mul_assoc, mul_div_mul_left _ _ (three_ne_zero' F), mul_right_comm 3 (b - d),
      ← neg_sub b d, mul_neg, neg_le, neg_add', neg_mul, neg_neg, ← mul_sub, ← abs_mul]
    apply le_of_abs_le
    replace X : 0 ≤ (3 : F) := zero_le_three
    rw [abs_mul, mul_assoc, abs_mul, div_eq_mul_inv (3 * |_|), abs_eq_self.mpr X]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg X (abs_nonneg _))
    apply (group_ineq (div_pos hy (mul_pos (add_pos hy hb) (add_pos hy hd))).le
      (div_pos hz (mul_pos (add_pos hz hc) (add_pos hz ha))).le).trans (max_le ?_ ?_)
    · generalize a + c = y at hy ⊢
      replace X : 0 < (y + b) * (y + d) := mul_pos (add_pos hy hb) (add_pos hy hd)
      have X0 : 0 < y * (y + (b + d)) := mul_pos hy (add_pos hy hz)
      rw [← div_mul_cancel_left₀ hy.ne.symm, div_le_div_iff_of_pos_left hy X X0,
        ← add_assoc, mul_comm, add_mul, mul_comm d, mul_add, add_le_add_iff_left]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hb.le) hd.le
    · generalize b + d = z at hz ⊢
      replace X : 0 < (z + c) * (z + a) := mul_pos (add_pos hz hc) (add_pos hz ha)
      have X0 : 0 < z * (a + c + z) := mul_pos hz (add_pos hy hz)
      rw [← div_mul_cancel_left₀ hz.ne.symm, div_le_div_iff_of_pos_left hz X X0,
        ← add_rotate, mul_add, add_mul, add_le_add_iff_left, mul_comm]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ha.le) hc.le

omit ha hb hc hd in
/-- Weakening of the lower bound -/
theorem lower_bound_weakening (x y : F) :
    (x + y) ^ 2 ≤ 4 * (x + y) ^ 2 - 9 * (x * y) := by
  have X : (9 : F) = 3 * 3 := by norm_num
  have h : 4 * ((x + y) ^ 2 - 3 * (x * y)) = (x + y) ^ 2 + 3 * (x - y) ^ 2 := by ring
  rw [X, ← three_add_one_eq_four, add_one_mul (3 : F),
    add_sub_right_comm, mul_assoc, ← mul_sub, le_add_iff_nonneg_left,
    ← mul_nonneg_iff_of_pos_left zero_lt_four, mul_left_comm, h]
  replace X : (0 : F) ≤ 3 := zero_le_three
  exact mul_nonneg X (add_nonneg (sq_nonneg _) (mul_nonneg X (sq_nonneg _)))

/-- A nicer but much weaker lower bound -/
theorem lower_bound_weaker :
    (|a - c| + |b - d|) ^ 2 / (6 * ((a + c) + (b + d)))
      ≤ (a - b) * (a - c) / (a + b + c) + (b - c) * (b - d) / (b + c + d)
        + (c - d) * (c - a) / (c + d + a) + (d - a) * (d - b) / (d + a + b) :=
  (lower_bound ha hb hc hd).trans' <| div_le_div_of_nonneg_right (lower_bound_weakening _ _)
    (mul_nonneg (by norm_num) (add_nonneg (add_nonneg ha.le hc.le) (add_nonneg hb.le hd.le)))

/-- Final solution, part 1 -/
theorem final_solution_part1 :
    0 ≤ (a - b) * (a - c) / (a + b + c) + (b - c) * (b - d) / (b + c + d)
      + (c - d) * (c - a) / (c + d + a) + (d - a) * (d - b) / (d + a + b) :=
  (lower_bound_weaker ha hb hc hd).trans' <| div_nonneg (sq_nonneg _)
    (mul_nonneg (by norm_num) (add_nonneg (add_nonneg ha.le hc.le) (add_nonneg hb.le hd.le)))

/-- Final solution, part 2 -/
theorem final_solution_part2 :
    (a - b) * (a - c) / (a + b + c) + (b - c) * (b - d) / (b + c + d)
      + (c - d) * (c - a) / (c + d + a) + (d - a) * (d - b) / (d + a + b) = 0 ↔
      a = c ∧ b = d := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · apply (lower_bound_weaker ha hb hc hd).trans_eq at h
    have X : 0 < 6 * (a + c + (b + d)) :=
      mul_pos (by norm_num) (add_pos (add_pos ha hc) (add_pos hb hd))
    rw [div_le_iff₀ X, zero_mul] at h
    apply (sq_nonneg _).antisymm at h
    rw [eq_comm, sq_eq_zero_iff, add_eq_zero_iff_of_nonneg (abs_nonneg _) (abs_nonneg _)] at h
    replace X {u v : F} (h : |u - v| = 0) : u = v := by rwa [abs_eq_zero, sub_eq_zero] at h
    exact And.imp X X h
  · rw [h.1, h.2, sub_self, sub_self, mul_zero, mul_zero]
    simp only [zero_div, zero_add]
