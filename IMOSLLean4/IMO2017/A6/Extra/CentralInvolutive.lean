/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs

/-!
# Central involutive elements of a monoid

Let $M$ be a monoid.
We construct the set $M[2]$ of central involutive elements of $M$.
We also prove that $M[2]$ is an abelian group.

TODO: Remove this if something similar gets to mathlib.
-/

namespace IMOSL
namespace IMO2017A6

/-- Central involutive elements -/
@[ext] structure CentralInvolutive (M) [Monoid M] where
  val : M
  mul_self_eq_one : val * val = 1
  mul_comm x : val * x = x * val


namespace CentralInvolutive

variable [Monoid M]

instance : CoeHead (CentralInvolutive M) M := ⟨val⟩

protected def one : CentralInvolutive M where
  val := 1
  mul_self_eq_one := mul_one 1
  mul_comm x := by rw [mul_one, one_mul]

instance : One (CentralInvolutive M) := ⟨CentralInvolutive.one⟩

@[simp] theorem one_val : (1 : CentralInvolutive M).val = 1 := rfl

protected def mul (x y : CentralInvolutive M) : CentralInvolutive M where
  val := x * y
  mul_self_eq_one := by rw [mul_assoc, x.mul_comm y, ← mul_assoc y.1, y.2, one_mul, x.2]
  mul_comm z := by rw [mul_assoc, y.3, x.3, mul_assoc, y.3]

instance : Mul (CentralInvolutive M) := ⟨CentralInvolutive.mul⟩

@[simp] theorem mul_val (x y : CentralInvolutive M) : (x * y).val = x.val * y.val := rfl

instance : Inv (CentralInvolutive M) := ⟨id⟩

@[simp] theorem inv_eq (x : CentralInvolutive M) : x⁻¹ = x := rfl

instance : CommGroup (CentralInvolutive M) where
  mul_comm x y := CentralInvolutive.ext (x.mul_comm y)
  mul_assoc x y z := CentralInvolutive.ext (mul_assoc x.1 y.1 z.1)
  one_mul x := CentralInvolutive.ext (one_mul x.1)
  mul_one x := CentralInvolutive.ext (mul_one x.1)
  inv_mul_cancel x := CentralInvolutive.ext x.mul_self_eq_one

theorem sq_eq_one (x : CentralInvolutive M) : x ^ 2 = 1 :=
  (sq _).trans (CentralInvolutive.ext x.mul_self_eq_one)


section

variable [HasDistribNeg M]

protected def neg (x : CentralInvolutive M) : CentralInvolutive M where
  val := -x
  mul_self_eq_one := by rw [neg_mul_neg, x.mul_self_eq_one]
  mul_comm c := by rw [mul_neg, neg_mul, x.mul_comm]

instance : Neg (CentralInvolutive M) := ⟨CentralInvolutive.neg⟩

@[simp] theorem neg_val (x : CentralInvolutive M) : (-x).val = -x.val := rfl

@[simp] theorem neg_one_val : (-1 : CentralInvolutive M).val = -1 := rfl

instance : HasDistribNeg (CentralInvolutive M) where
  neg_neg x := CentralInvolutive.ext (neg_neg x.1)
  neg_mul x y := CentralInvolutive.ext (neg_mul x.1 y.1)
  mul_neg x y := CentralInvolutive.ext (mul_neg x.1 y.1)

end
