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
@[ext] structure CentralInvolutive (M) [MulOneClass M] where
  val : M
  val_mul_self_eq_one : val * val = 1
  val_mul_comm x : x * val = val * x


namespace CentralInvolutive

section

variable [MulOneClass M]

instance : CoeHead (CentralInvolutive M) M := ⟨val⟩

instance : One (CentralInvolutive M) :=
  ⟨⟨1, mul_one 1, λ _ ↦ by rw [mul_one, one_mul]⟩⟩

@[simp] theorem one_val : (1 : CentralInvolutive M).val = 1 := rfl

end


section

variable [Monoid M]

@[simp] theorem mul_mul_cancel_left (x : CentralInvolutive M) (y : M) : x * (x * y) = y := by
  rw [← mul_assoc, x.val_mul_self_eq_one, one_mul]

@[simp] theorem mul_mul_cancel_right (x : CentralInvolutive M) (y : M) : y * x * x = y := by
  rw [mul_assoc, x.val_mul_self_eq_one, mul_one]

theorem mul_mul_mul_cancel_left (x : CentralInvolutive M) (y z : M) :
    (x * y) * (x * z) = y * z := by
  rw [← x.val_mul_comm, mul_assoc, x.mul_mul_cancel_left]

theorem mul_mul_mul_cancel_right (x : CentralInvolutive M) (y z : M) :
    (y * x) * (z * x) = y * z := by
  rw [x.val_mul_comm, x.val_mul_comm, x.mul_mul_mul_cancel_left]

protected def mul (x y : CentralInvolutive M) : CentralInvolutive M where
  val := x * y
  val_mul_self_eq_one := by rw [x.mul_mul_mul_cancel_left, y.val_mul_self_eq_one]
  val_mul_comm z := by rw [← mul_assoc, y.val_mul_comm,
    x.val_mul_comm, ← mul_assoc, y.val_mul_comm]

instance : Mul (CentralInvolutive M) := ⟨CentralInvolutive.mul⟩

@[simp] theorem mul_val (x y : CentralInvolutive M) : (x * y).val = x.val * y.val := rfl

@[simp] theorem mul_self_eq_one (a : CentralInvolutive M) : a * a = 1 :=
  CentralInvolutive.ext a.val_mul_self_eq_one

theorem mul_comm (a b : CentralInvolutive M) : a * b = b * a :=
  CentralInvolutive.ext (b.val_mul_comm a)

instance : Inv (CentralInvolutive M) := ⟨id⟩

@[simp] theorem inv_eq (x : CentralInvolutive M) : x⁻¹ = x := rfl

instance : CommGroup (CentralInvolutive M) where
  mul_comm x y := CentralInvolutive.ext (y.val_mul_comm x)
  mul_assoc x y z := CentralInvolutive.ext (mul_assoc x.1 y.1 z.1)
  one_mul x := CentralInvolutive.ext (one_mul x.1)
  mul_one x := CentralInvolutive.ext (mul_one x.1)
  inv_mul_cancel x := CentralInvolutive.ext x.val_mul_self_eq_one

theorem sq_eq_one (x : CentralInvolutive M) : x ^ 2 = 1 :=
  (sq _).trans (CentralInvolutive.ext x.val_mul_self_eq_one)

end


section

variable [MulOneClass M] [HasDistribNeg M]

protected def neg (x : CentralInvolutive M) : CentralInvolutive M where
  val := -x
  val_mul_self_eq_one := by rw [neg_mul_neg, x.val_mul_self_eq_one]
  val_mul_comm c := by rw [mul_neg, neg_mul, x.val_mul_comm]

instance : Neg (CentralInvolutive M) := ⟨CentralInvolutive.neg⟩

@[simp] theorem neg_val (x : CentralInvolutive M) : (-x).val = -x.val := rfl

@[simp] theorem neg_one_val : (-1 : CentralInvolutive M).val = -1 := rfl

end


instance [Monoid M] [HasDistribNeg M] : HasDistribNeg (CentralInvolutive M) where
  neg_neg x := CentralInvolutive.ext (neg_neg x.1)
  neg_mul x y := CentralInvolutive.ext (neg_mul x.1 y.1)
  mul_neg x y := CentralInvolutive.ext (mul_neg x.1 y.1)





/-! ### Additional lemmas about central involutive elements -/

section

variable [Monoid M] (x : CentralInvolutive M) {y z : M}

theorem mul_left_inj : x * y = x * z ↔ y = z :=
  ⟨λ h ↦ by simpa only [mul_mul_cancel_left] using congrArg (x.1 * ·) h, congrArg (x.1 * ·)⟩

theorem mul_left_eq_iff_eq_mul : x * y = z ↔ y = x * z :=
  ⟨λ h ↦ h ▸ (x.mul_mul_cancel_left y).symm, λ h ↦ h ▸ x.mul_mul_cancel_left z⟩

theorem mul_right_eq_iff_eq_mul : y * x = z ↔ y = z * x :=
  ⟨λ h ↦ h ▸ (x.mul_mul_cancel_right y).symm, λ h ↦ h ▸ x.mul_mul_cancel_right z⟩

end
