/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Basic

/-! # More inequalities on rings -/

namespace IMOSL
namespace Extra

variable [LinearOrderedCommSemiring R] [ExistsAddOfLE R]

theorem two_sq_AM_GM (x y : R) : 2 ^ 2 * (x * y) ≤ (x + y) ^ 2 := by
  rw [sq, mul_assoc, two_mul, ← mul_assoc, add_sq', add_le_add_iff_right]
  exact two_mul_le_add_sq x y

theorem AM_GM_two {a x y : R} (h : 0 ≤ x + y) (ha : a ^ 2 ≤ x * y) :
    2 * a ≤ x + y := by
  refine le_of_pow_le_pow_left (Nat.succ_ne_zero 1) h ((two_sq_AM_GM x y).trans' ?_)
  rw [mul_pow]; exact mul_le_mul_of_nonneg_left ha (sq_nonneg _)

theorem CauchySchwarz_two {a b x y z w : R} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : a ^ 2 ≤ x * y) (hz : 0 ≤ z) (hw : 0 ≤ w) (hb : b ^ 2 ≤ z * w) :
    (a + b) ^ 2 ≤ (x + z) * (y + w) := by
  rw [add_sq, add_mul, mul_add, mul_add, ← add_assoc, add_assoc (x * y), mul_assoc]
  refine add_le_add_three ha (AM_GM_two ?_ ?_) hb
  · exact add_nonneg (mul_nonneg hx hw) (mul_nonneg hz hy)
  · rw [mul_pow, mul_comm z, mul_mul_mul_comm, mul_comm w]
    exact mul_le_mul ha hb (sq_nonneg b) (mul_nonneg hx hy)
