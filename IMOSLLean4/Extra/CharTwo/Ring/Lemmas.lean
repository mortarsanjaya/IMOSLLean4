/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.CharTwo.Ring.Basic
import Mathlib.Algebra.GroupPower.Basic

/-!
# Characteristic two (semi)rings

We prove several lemmas about `CharTwo` semirings.
This is separated from non-associative version as it needs an extra import,
  `Mathlib.Algebra.GroupPower.Basic`.
-/

namespace IMOSL
namespace Extra
namespace CharTwo

section

variable [Semiring R] [CharTwo R]

lemma add_sq_of_Commute {x y : R} (h : x * y = y * x) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  rw [sq, sq, sq, add_mul_self_of_Commute h]

lemma add_one_sq (x : R) : (x + 1) ^ 2 = x ^ 2 + 1 := by
  rw [sq, sq, add_one_mul_self]

lemma sq_eq_one_iff [NoZeroDivisors R] {x : R} : x ^ 2 = 1 ↔ x = 1 := by
  rw [sq, mul_self_eq_one_iff]

end





/-! ### Commutative semiring -/

section

variable [CommSemiring R] [CharTwo R]

lemma add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  add_sq_of_Commute (mul_comm x y)

lemma sq_eq_iff [NoZeroDivisors R] {x y : R} : x ^ 2 = y ^ 2 ↔ x = y := by
  rw [sq, sq, mul_self_eq_iff]

end
