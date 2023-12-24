/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5Basic
import Mathlib.Algebra.GroupPower.Ring

/-!
# IMO 2012 A5, Case 2: $f(-1) = 0$ (Basic Results)

This file collects basic results in Case 2.
-/

namespace IMOSL
namespace IMO2012A5

variable [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0)

/-- (6.1) `f` is even -/
theorem case2_map_even (x : R) : f (-x) = f x :=
  by rw [← sub_eq_zero, map_neg_sub_map2 h, h0, mul_zero]

/-- (6.2) -/
theorem case2_good_alt (x y : R) : f (x * y - 1) - f (x - y) = f x * f y := by
  have h1 := case2_map_even h h0
  rw [← h1 y, ← h, ← sub_eq_add_neg, mul_neg, neg_add_eq_sub, ← neg_sub 1, h1]

/-- (6.3) -/
theorem case2_map_sq_sub_one (h3 : f 0 = -1) (x : R) :
    f (x ^ 2 - 1) = f x ^ 2 - 1 := by
  rw [sq, sq, ← case2_good_alt h h0, sub_self, h3, sub_neg_eq_add, add_sub_cancel]

/-- (6.4) -/
theorem case2_map_self_mul_add_one_sub_one (x : R) :
    f (x * (x + 1) - 1) = f x * f (x + 1) := by
  rw [← case2_good_alt h h0, sub_add_cancel', h0, sub_zero]

/-- (6.5) -/
theorem case2_map_add_two_eq (x : R) :
    f (x + 2) = f 2 * (f (x + 1) - f x) + f (x - 1) := by
  have h2 := case2_map_even h h0
  have h3 := λ t ↦ eq_add_of_sub_eq (h 2 t)
  rw [add_comm, mul_sub, ← add_sub_right_comm, eq_sub_iff_add_eq', ← h3,
    ← h2, ← add_sub_cancel (2 * x + 1) 1, neg_sub', sub_neg_eq_add, add_assoc,
    one_add_one_eq_two, ← mul_add_one 2 x, ← mul_neg, h3, h2, add_right_inj, ← h2,
    ← sub_eq_add_neg, neg_sub, ← one_add_one_eq_two, add_sub_add_right_eq_sub]

/-- (6.6) -/
theorem case2_special_identity (x : R) :
    f x * f (x + 1) - f (x - 1) * f (x + 2) = f x * f 2 + f (x + 2) := by
  rw [← case2_map_self_mul_add_one_sub_one h h0, ← h, ← h, sub_add_cancel,
    mul_two, ← sub_add, ← one_add_one_eq_two, ← add_assoc,
    sub_add_add_cancel, ← add_assoc, add_left_eq_self, sub_eq_zero]
  apply congr_arg f
  rw [sub_eq_iff_eq_add, mul_add_one (x - 1), add_assoc _ (x - 1),
    sub_add_cancel, add_assoc, sub_one_mul, sub_add_cancel]
