/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring

/-!
# IMO 2006 A6 (P3)

Find the smallest $M ∈ ℝ$ such that for any $a, b, c ∈ ℝ$,
$$ |ab(a^2 - b^2) + bc(b^2 - c^2) + ca(c^2 - a^2)| ≤ M(a^2 + b^2 + c^2)^2. $$
-/

namespace IMOSL
namespace IMO2006A6

def good [LinearOrderedCommRing R] (M : R) :=
  ∀ a b c : R, |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)|
    ≤ M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2



theorem ring_id1 [CommRing R] (a b c : R) :
    a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)
      = (b - a) * (c - b) * (a - c) * (a + b + c) := by ring

theorem ring_id2 [CommRing R] (a b c : R) :
    (b - a) ^ 2 + (c - b) ^ 2 + (a - c) ^ 2 + (a + b + c) ^ 2
      = 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring



section

variable [LinearOrderedCommRing R]

theorem good_alt {M : R} :
    good M ↔ ∀ a b c, 3 ^ 2 * |(b - a) * (c - b) * (a - c) * (a + b + c)|
      ≤ M * ((b - a) ^ 2 + (c - b) ^ 2 + (a - c) ^ 2 + (a + b + c) ^ 2) ^ 2 :=
  forall_congr' λ a ↦ forall_congr' λ b ↦ forall_congr' λ c ↦ by
    have X0 : (0 : R) < 3 ^ 2 := pow_pos zero_lt_three 2
    rw [ring_id1, ring_id2, mul_pow, mul_left_comm, mul_le_mul_iff_of_pos_left X0]

theorem ring_ineq1 (r t : R) : 2 ^ 8 * (r ^ 3 * t) ≤ 3 ^ 3 * (r + t) ^ 4 :=
  le_of_sub_nonneg <| by calc
    0 ≤ (r - 3 * t) ^ 2 * ((5 * r + t) ^ 2 + 2 * (r + t) ^ 2) :=
      mul_nonneg (sq_nonneg _) <| add_nonneg (sq_nonneg _) <|
        mul_nonneg zero_le_two (sq_nonneg _)
    _ = _ := by ring

theorem ring_ineq2 {x y z : R} (h : x + y + z = 0) :
    2 * 3 ^ 3 * (x * y * z) ^ 2 ≤ (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 :=
  le_of_sub_nonneg <| by calc
    0 ≤ 2 * ((x - y) * (x + 2 * y) * (2 * x + y)) ^ 2 := mul_nonneg zero_le_two (sq_nonneg _)
    _ = (x ^ 2 + y ^ 2 + (-(x + y)) ^ 2) ^ 3 - 2 * 3 ^ 3 * (x * y * -(x + y)) ^ 2 := by ring
    _ = _ := by rw [eq_neg_of_add_eq_zero_right h]

theorem ring_ineq3 (a b c : R) :
    2 ^ 9 * ((b - a) * (c - b) * (a - c) * (a + b + c)) ^ 2
      ≤ ((b - a) ^ 2 + (c - b) ^ 2 + (a - c) ^ 2 + (a + b + c) ^ 2) ^ 4 := by
  refine le_of_mul_le_mul_left ?_ (pow_pos zero_lt_three 3)
  rw [mul_left_comm, pow_succ, mul_assoc, ← mul_assoc 2, mul_pow, ← mul_assoc (2 * _)]
  refine (ring_ineq1 _ _).trans' <| mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (ring_ineq2 ?_) (sq_nonneg _)) (pow_nonneg zero_le_two 8)
  rw [sub_add_sub_cancel', sub_add_sub_cancel, sub_self]



class HasSqrt2 (R) [LinearOrderedCommRing R] where
  sqrt2 : R
  sqrt2_nonneg : 0 ≤ sqrt2
  sqrt2_sq : sqrt2 ^ 2 = 2

notation : max "√2" => HasSqrt2.sqrt2

open HasSqrt2

variable [HasSqrt2 R] {M : R}

theorem good_lower_bound (hM : 3 ^ 2 * √2 ≤ 2 ^ 5 * M) : good M := good_alt.mpr λ a b c ↦ by
  have h : (0 : R) < 2 := two_pos
  rw [← mul_le_mul_iff_of_pos_left (pow_pos h 5), mul_left_comm, ← mul_assoc _ M]
  apply (mul_le_mul_of_nonneg_right hM (sq_nonneg _)).trans'
  rw [mul_assoc (3 ^ 2), mul_le_mul_iff_of_pos_left (pow_pos zero_lt_three 2),
    ← abs_of_nonneg h.le, ← abs_of_nonneg (sqrt2_nonneg (R := R)), pow_abs,
    ← abs_mul, ← abs_sq, ← abs_mul, ← sq_le_sq, mul_pow, mul_pow √2, sqrt2_sq,
    ← pow_mul, ← pow_mul, pow_succ', mul_assoc]
  exact mul_le_mul_of_nonneg_left (ring_ineq3 a b c) h.le

theorem good_upper_bound (hM : good M) : 9 * sqrt2 ≤ 32 * M := by
  specialize hM (√2 - 3) (√2 + 3) √2
  rw [ring_id1, add_sub_sub_cancel, sub_add_cancel_left, sub_sub_cancel_left, ← two_mul,
    mul_assoc (2 * 3), ← sq, neg_sq, sub_add_add_cancel, ← two_mul, ← add_one_mul (2 : R),
    sub_sq', add_sq' √2, sub_add_add_cancel, sqrt2_sq, ← mul_assoc, abs_mul] at hM
  have h : |2 * 3 * 3 ^ 2 * (2 + 1)| = (18 * 9 : R) := by norm_num
  have h0 : (2 + 3 ^ 2 + (2 + 3 ^ 2) + 2) ^ 2 = (18 * 32 : R) := by norm_num
  rw [h, h0, mul_comm M, mul_assoc, mul_assoc, abs_of_nonneg sqrt2_nonneg] at hM
  exact le_of_mul_le_mul_left hM (by norm_num)

theorem good_iff : good M ↔ 9 * sqrt2 ≤ 32 * M :=
  ⟨good_upper_bound, by
    have h : (9 : R) = 3 ^ 2 := by norm_num
    have h0 : (32 : R) = 2 ^ 5 := by norm_num
    rw [h, h0]; exact good_lower_bound⟩

end





/-- Final solution -/
theorem final_solution [LinearOrderedField F] [HasSqrt2 F] {M : F} :
    good M ↔ 9 * √2 / 32 ≤ M :=
  good_iff.trans (div_le_iff' (by norm_num : 0 < (32 : F))).symm
