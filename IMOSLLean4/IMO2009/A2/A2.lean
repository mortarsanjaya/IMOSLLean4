/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring

/-!
# IMO 2009 A2

Let $F$ be a totally ordered field, and $a, b, c ∈ F$ be positive elements.
Prove that
$$ \frac{1}{(2a + b + c)^2} + \frac{1}{(2b + c + a)^2} + \frac{1}{(2c + a + b)^2}
  ≤ \frac{3}{16}. $$
-/

namespace IMOSL
namespace IMO2009A2

/-! ### Ring identities -/

section

variable [CommRing R]

theorem ring_identity1 (a b c : R) :
    (a + b) * (b + c) * (c + a) + a * b * c
      = (a + b + c) * (a * b + b * c + c * a) := by ring

theorem ring_identity2 (a b c : R) :
    2 * ((a * b + b * c + c * a) ^ 2 - 3 * (a * b * c * (a + b + c))) =
      (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2 := by ring

theorem ring_identity3 (a b c : R) : (a + b) + (c + a) + (b + c) = 2 * (a + b + c) := by ring

end



/- ### Ring inequalities -/

section

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem ring_ineq1 (a b : R) : 2 ^ 2 * (a * b) ≤ (a + b) ^ 2 := by
  rw [add_sq', sq, two_mul, add_mul, ← mul_assoc, add_le_add_iff_right]
  exact two_mul_le_add_sq a b

theorem ring_ineq2 {a b c : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    2 ^ 3 * (a * b * c) ≤ (a + b) * (b + c) * (c + a) := by
  have X {x y : R} : 0 ≤ x → 0 ≤ y → 0 ≤ x * y := mul_nonneg
  have Y {x y : R} : 0 ≤ x → 0 ≤ y → 0 ≤ x + y := add_nonneg
  apply le_of_pow_le_pow_left₀ (Nat.succ_ne_zero 1) (X (X (Y ha hb) (Y hb hc)) (Y hc ha))
  replace Y (x : R) : 0 ≤ x ^ 2 := sq_nonneg x
  let Z := ring_ineq1 (R := R)
  have Y2 := Y 2
  calc
    _ = (2 ^ 2 * (a * b)) * (2 ^ 2 * (b * c)) * (2 ^ 2 * (c * a)) := by ring
    _ ≤ (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 :=
      mul_le_mul (mul_le_mul (Z a b) (Z b c) (X Y2 (X hb hc)) (Y _))
        (Z c a) (X Y2 (X hc ha)) (X (Y _) (Y _))
    _ = _ := by rw [mul_pow, mul_pow]

theorem ring_ineq3 {a b c : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (2 ^ 3) * ((a + b + c) * (a * b + b * c + c * a))
      ≤ (3 * 3) * ((a + b) * (b + c) * (c + a)) := by
  have X : (3 * 3 : R) = 2 ^ 3 + 1 := by norm_num
  rw [X, add_one_mul, ← ring_identity1, mul_add, add_le_add_iff_left]
  exact ring_ineq2 ha hb hc

theorem ring_ineq4 (a b c : R) :
    3 * (a * b * c * (a + b + c)) ≤ (a * b + b * c + c * a) ^ 2 := by
  rw [← sub_nonneg, ← mul_nonneg_iff_of_pos_left zero_lt_two, ring_identity2]
  exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

theorem ring_ineq5 {a b c : R} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < a * b + b * c + c * a :=
  add_pos (add_pos (mul_pos ha hb) (mul_pos hb hc)) (mul_pos hc ha)

end



/-! ### Field identities -/

section

variable [Field F] {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
include ha hb hc

theorem field_identity1 : (a * b)⁻¹ + (b * c)⁻¹ + (c * a)⁻¹ = (a + b + c) / (a * b * c) := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  rw [eq_div_iff_mul_eq (mul_ne_zero hab hc), add_mul, add_mul, add_rotate,
    inv_mul_cancel_left₀ hab, mul_rotate, inv_mul_cancel_left₀ (mul_ne_zero hb hc),
    mul_rotate, inv_mul_cancel_left₀ (mul_ne_zero hc ha)]

theorem field_identity2 : a * b * c * (a⁻¹ + b⁻¹ + c⁻¹) = a * b + b * c + c * a := by
  rw [← add_rotate, mul_add, mul_add, mul_inv_cancel_right₀ hc, mul_rotate a,
    mul_inv_cancel_right₀ ha, mul_rotate b, mul_inv_cancel_right₀ hb]

end



/-! ### Field inequalities -/

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {a b c : F} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
include ha hb hc

theorem field_ineq1 : ((2 * a + b + c) ^ 2)⁻¹ ≤ (2 ^ 2 * ((a + b) * (a + c)))⁻¹ := by
  rw [two_mul, add_assoc, add_add_add_comm]
  have hab : 0 < a + b := add_pos ha hb
  have hac : 0 < a + c := add_pos ha hc
  refine (inv_le_inv₀ (pow_pos (add_pos hab hac) 2) ?_).mpr (ring_ineq1 _ _)
  exact mul_pos (pow_pos (zero_lt_two' F) 2) (mul_pos hab hac)

theorem field_ineq2 :
    ((2 * a + b + c) ^ 2)⁻¹ + ((2 * b + c + a) ^ 2)⁻¹ + ((2 * c + a + b) ^ 2)⁻¹
      ≤ (a + b + c) / (2 * ((a + b) * (b + c) * (c + a))) := by
  have X {a b c : F} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) := field_ineq1 ha hb hc
  apply (add_le_add_three (X ha hb hc) (X hb hc ha) (X hc ha hb)).trans_eq
  have hab : a + b ≠ 0 := (add_pos ha hb).ne.symm
  have hbc : b + c ≠ 0 := (add_pos hb hc).ne.symm
  have hca : c + a ≠ 0 := (add_pos hc ha).ne.symm
  rw [mul_inv, mul_inv (2 ^ 2), mul_inv (2 ^ 2), ← mul_add, ← mul_add, add_comm a c,
    add_comm b a, add_comm c b, add_right_comm, field_identity1 hab hca hbc,
    ← one_div, div_mul_div_comm, one_mul, ring_identity3, sq, mul_assoc,
    mul_div_mul_left _ _ (two_ne_zero' F), mul_right_comm]

theorem field_ineq3 :
    (a + b + c) / (2 * ((a + b) * (b + c) * (c + a)))
      ≤ (3 * 3) / (16 * (a * b + b * c + c * a)) := by
  have X : (16 : F) = 2 * 2 ^ 3 := by norm_num
  have h := mul_pos (mul_pos (add_pos ha hb) (add_pos hb hc)) (add_pos hc ha)
  have h0 := mul_pos (pow_pos (zero_lt_two' F) 3) (ring_ineq5 ha hb hc)
  rw [X, mul_assoc 2, mul_comm, ← div_div, mul_comm 2, ← div_div _ _ 2,
    div_le_div_iff_of_pos_right (zero_lt_two' F), div_le_div_iff₀ h h0, mul_left_comm]
  exact ring_ineq3 ha.le hb.le hc.le

theorem field_ineq4 :
    ((2 * a + b + c) ^ 2)⁻¹ + ((2 * b + c + a) ^ 2)⁻¹ + ((2 * c + a + b) ^ 2)⁻¹
      ≤ (3 * 3) / (16 * (a * b + b * c + c * a)) :=
  (field_ineq2 ha hb hc).trans (field_ineq3 ha hb hc)

theorem field_ineq5 (h : a⁻¹ + b⁻¹ + c⁻¹ = a + b + c) : 3 ≤ a * b + b * c + c * a := by
  have h0 := ring_ineq4 a b c
  rw [← h, field_identity2 ha.ne.symm hb.ne.symm hc.ne.symm, sq] at h0
  exact le_of_mul_le_mul_right h0 (ring_ineq5 ha hb hc)





/-! ### Summary -/

/-- Final solution -/
theorem final_solution (h : a⁻¹ + b⁻¹ + c⁻¹ = a + b + c) :
    ((2 * a + b + c) ^ 2)⁻¹ + ((2 * b + c + a) ^ 2)⁻¹ + ((2 * c + a + b) ^ 2)⁻¹ ≤ 3 / 16 := by
  apply (field_ineq4 ha hb hc).trans
  have h0 := field_ineq5 ha hb hc h
  have X : (0 : F) < 3 / 16 := by norm_num
  rwa [mul_div_mul_comm, mul_le_iff_le_one_right X,
    div_le_one ((zero_lt_three' F).trans_le h0)]
