/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.Ring.Basic

/-!
# IMO 2008 A5

Let $F$ be a totally ordered field and $a_1, a_2, a_3, a_4 ∈ F$ be positive elements.
Suppose that $a_1 a_2 a_3 a_4 = 1$ and
$$ \sum_{i = 1}^4 a_i > \sum_{i = 1}^4 \frac{a_i}{a_{i + 1}}. $$
Prove that
$$ \sum_{i = 1}^4 a_i < \sum_{i = 1}^4 \frac{a_{i + 1}}{a_i}. $$
-/

namespace IMOSL
namespace IMO2008A5

lemma ring_ineq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (a b : R) :
    2 ^ 2 * (a * b) ≤ (a + b) ^ 2 := by
  rw [sq, mul_assoc, two_mul, ← mul_assoc, add_sq', add_le_add_iff_right]
  exact two_mul_le_add_sq a b


variable [Semifield F] [LinearOrder F] [IsStrictOrderedRing F] [ExistsAddOfLE F]
  {a b c d : F} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
include ha hb hc hd

lemma ineq1 : (4 * a) ^ 4 / (a * b * c * d) ≤ (2 * (a / b) + (b / c + a / d)) ^ 4 := by
  have X : 4 = (2 : F) ^ 2 := by rw [← Nat.cast_ofNat, ← Nat.cast_two, ← Nat.cast_pow]; rfl
  ---- Split calculation, part 1 (for responsiveness)
  calc (4 * a) ^ 4 / (a * b * c * d)
    _ = (4 * (2 * (a / b))) ^ 2 * (2 ^ 2 * ((b / c) * (a / d))) := ?_
    _ ≤ (4 * (2 * (a / b))) ^ 2 * (b / c + a / d) ^ 2 :=
      mul_le_mul_of_nonneg_left (ring_ineq _ _) (sq_nonneg _)
    _ = (2 ^ 2 * (2 * (a / b) * (b / c + a / d))) ^ 2 := by rw [← mul_pow, X, mul_assoc]
    _ ≤ ((2 * (a / b) + (b / c + a / d)) ^ 2) ^ 2 := by
      refine pow_le_pow_left₀ (mul_nonneg (sq_nonneg 2) ?_) (ring_ineq _ _) 2
      have X {u v : F} (hu : 0 < u) (hv : 0 < v) : 0 < u / v := div_pos hu hv
      exact mul_nonneg (mul_nonneg zero_le_two (X ha hb).le) (add_pos (X hb hc) (X ha hd)).le
    _ = _ := by rw [← pow_mul]
  ---- Split calculation, part 2
  calc
    _ = 4 ^ 4 * (a ^ 3 / (b * c * d)) := by
      rw [mul_pow, mul_div_assoc, pow_succ' a, mul_assoc a,
        mul_assoc a, mul_div_mul_left _ _ ha.ne.symm]
    _ = 4 ^ 4 * (a / b * (a / c) * (a / d)) := by
      rw [div_mul_div_comm, div_mul_div_comm, ← sq, ← pow_succ]
    _ = 4 ^ 4 * ((a / b) ^ 2 * ((b / c) * (a / d))) := by
      rw [sq, mul_mul_mul_comm, div_mul_div_cancel₀ hb.ne.symm,
        mul_left_comm (a / c), mul_assoc]
    _ = 4 ^ 2 * ((2 * (a / b)) ^ 2 * (2 ^ 2 * ((b / c) * (a / d)))) := by
      rw [mul_pow, ← X, mul_mul_mul_comm, ← sq, ← mul_assoc (4 ^ 2), ← pow_add]
    _ = (4 * (2 * (a / b))) ^ 2 * (2 ^ 2 * ((b / c) * (a / d))) := by
      rw [← mul_assoc, ← mul_pow]

variable (h : a * b * c * d = 1)
include h

lemma ineq2 : 4 * a ≤ 2 * (a / b) + (b / c + a / d) := by
  have h0 := ineq1 ha hb hc hd
  rw [h, div_one] at h0
  refine le_of_pow_le_pow_left₀ (Nat.succ_ne_zero 3) ?_ h0
  exact (add_pos (mul_pos two_pos (div_pos ha hb))
    (add_pos (div_pos hb hc) (div_pos ha hd))).le

lemma main_ineq : 4 * (a + b + c + d) ≤
    3 * (a / b + b / c + c / d + d / a) + (b / a + c / b + d / c + a / d) := calc
  _ = 4 * a + 4 * b + 4 * c + 4 * d := by rw [mul_add, mul_add, mul_add]
  _ ≤ (2 * (a / b) + (b / c + a / d)) + (2 * (b / c) + (c / d + b / a))
      + (2 * (c / d) + (d / a + c / b)) + (2 * (d / a) + (a / b + d / c)) := by
    refine add_le_add (add_le_add_three ?_ ?_ ?_) ?_
    all_goals apply ineq2 <;> try assumption
    · rw [mul_comm, ← mul_assoc, ← mul_assoc, h]
    · rw [mul_assoc, mul_comm, ← mul_assoc, h]
    · rw [mul_rotate d, mul_right_comm, h]
  _ = _ := by
    rw [add_add_add_comm (2 * _), ← mul_add, add_add_add_comm (2 * _),
      ← mul_add, add_add_add_comm (2 * _), ← mul_add, add_add_add_comm (b / c),
      add_add_add_comm (b / c + c / d), add_add_add_comm (_ + _ + _),
      ← two_add_one_eq_three, add_one_mul, add_assoc (2 * _), add_right_inj]
    refine congrArg₂ _ ?_ ?_
    · rw [add_comm, ← add_assoc, ← add_assoc]
    · rw [add_rotate (a / d), add_right_comm]

/-- Final solution -/
theorem final_solution (h0 : a / b + b / c + c / d + d / a < a + b + c + d) :
    a + b + c + d < b / a + c / b + d / c + a / d := by
  refine lt_of_not_ge λ h1 ↦ (main_ineq ha hb hc hd h).not_gt ?_
  rw [← three_add_one_eq_four, add_one_mul]
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h0 three_pos) h1
