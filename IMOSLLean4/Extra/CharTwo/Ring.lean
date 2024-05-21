/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.CharTwo.Defs
import Mathlib.Algebra.Ring.Defs

/-!
# Characteristic two (semi)rings

We prove several lemmas about semirings of characteristic two (using `CharTwo`).
-/

namespace IMOSL
namespace Extra
namespace CharTwo

theorem Semiring_of_two_eq_zero [Semiring R] (h : (2 : R) = 0) : CharTwo R :=
  ⟨λ x ↦ by rw [← two_mul, h, zero_mul]⟩


section

variable [Semiring R] [CharTwo R]

theorem two_eq_zero : (2 : R) = 0 := by
  rw [← one_add_one_eq_two, add_self_eq_zero]

lemma add_mul_self_of_Commute {x y : R} (h : x * y = y * x) :
    (x + y) * (x + y) = x * x + y * y := by
  rw [add_mul, mul_add, mul_add, ← add_assoc, h, add_add_cancel_right]

lemma add_one_mul_self (x : R) : (x + 1) * (x + 1) = x * x + 1 := by
  rw [add_mul_self_of_Commute ((mul_one x).trans (one_mul x).symm), one_mul]

end





/-! ### Commutative semiring -/

section

variable [CommSemiring R] [CharTwo R]

lemma add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y :=
  add_mul_self_of_Commute (mul_comm x y)

end