/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Mathlib.Algebra.CharP.Two

/-!
# Explicit construction of `𝔽₄`

In this file, we explicitly construct `𝔽₄`, the field of 4 elements.
We prove that it is a ring, and we construct ring homomorphisms from `𝔽₄`.

### TODO

Unify with `IMOSLLean4.Extra.ExplicitRings.F4`.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

inductive 𝔽₄
  | O : 𝔽₄
  | I : 𝔽₄
  | X : 𝔽₄
  | Y : 𝔽₄


namespace 𝔽₄

protected def add : 𝔽₄ → 𝔽₄ → 𝔽₄
  | O, x => x
  | I, O => I
  | I, I => O
  | I, X => Y
  | I, Y => X
  | X, O => X
  | X, I => Y
  | X, X => O
  | X, Y => I
  | Y, O => Y
  | Y, I => X
  | Y, X => I
  | Y, Y => O

protected def mul : 𝔽₄ → 𝔽₄ → 𝔽₄
  | O, _ => O
  | I, x => x
  | X, O => O
  | X, I => X
  | X, X => Y
  | X, Y => I
  | Y, O => O
  | Y, I => Y
  | Y, X => I
  | Y, Y => X

instance : Zero 𝔽₄ := ⟨O⟩
instance : One 𝔽₄ := ⟨I⟩
instance : Add 𝔽₄ := ⟨𝔽₄.add⟩
instance : Neg 𝔽₄ := ⟨id⟩
instance : Mul 𝔽₄ := ⟨𝔽₄.mul⟩

instance : DecidableEq 𝔽₄
  | O, O => isTrue rfl
  | O, I => isFalse noConfusion
  | O, X => isFalse noConfusion
  | O, Y => isFalse noConfusion
  | I, O => isFalse noConfusion
  | I, I => isTrue rfl
  | I, X => isFalse noConfusion
  | I, Y => isFalse noConfusion
  | X, O => isFalse noConfusion
  | X, I => isFalse noConfusion
  | X, X => isTrue rfl
  | X, Y => isFalse noConfusion
  | Y, O => isFalse noConfusion
  | Y, I => isFalse noConfusion
  | Y, X => isFalse noConfusion
  | Y, Y => isTrue rfl

instance : Fintype 𝔽₄ where
  elems := {O, I, X, Y}
  complete x := by cases x <;> decide

/-- `𝔽₄` is a commutative group. -/
instance : AddCommGroup 𝔽₄ where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `𝔽₄` is a commutative ring. -/
instance : CommRing 𝔽₄ where
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  left_distrib := by decide
  right_distrib := by decide



/-! ### Ring homomorphism from `𝔽₄` -/

def cast [AddMonoidWithOne R] (r : R) : 𝔽₄ → R
  | O => 0
  | I => 1
  | X => r
  | Y => r + 1

variable [NonAssocSemiring R] [CharP R 2]

theorem cast_add (r : R) (x y) : cast r (x + y) = cast r x + cast r y := by
  match x, y with
  | O, _ => exact (zero_add _).symm
  | I, O => exact (add_zero _).symm
  | I, I => exact (CharTwo.add_self_eq_zero _).symm
  | I, X => exact add_comm _ _
  | I, Y => change r = 1 + (r + 1); rw [add_comm, CharTwo.add_cancel_right]
  | X, O => exact (add_zero _).symm
  | X, I => rfl
  | X, X => exact (CharTwo.add_self_eq_zero _).symm
  | X, Y => exact (CharTwo.add_cancel_left _ _).symm
  | Y, O => exact (add_zero _).symm
  | Y, I => exact (CharTwo.add_cancel_right _ _).symm
  | Y, X => change 1 = r + 1 + r; rw [add_comm, CharTwo.add_cancel_left]
  | Y, Y => exact (CharTwo.add_self_eq_zero _).symm

variable {r : R} (h : r * r + r = 1)
include h

theorem cast_mul (x y) : cast r (x * y) = cast r x * cast r y := by
  match x, y with
  | O, _ => exact (zero_mul _).symm
  | I, _ => exact (one_mul _).symm
  | X, O => exact (mul_zero _).symm
  | X, I => exact (mul_one _).symm
  | X, X => rwa [CharTwo.add_eq_iff_eq_add, add_comm, eq_comm] at h
  | X, Y => rwa [← mul_add_one, eq_comm] at h
  | Y, O => exact (mul_zero _).symm
  | Y, I => exact (mul_one _).symm
  | Y, X => rwa [← add_one_mul, eq_comm] at h
  | Y, Y => change r = (r + 1) * (r + 1)
            rw [mul_add_one, add_one_mul, h, add_comm, CharTwo.add_cancel_right]

def castRingHom : 𝔽₄ →+* R where
  toFun := cast r
  map_one' := rfl
  map_mul' := cast_mul h
  map_zero' := rfl
  map_add' := cast_add r

theorem castRingHom_injective (h0 : (1 : R) ≠ 0) : Function.Injective (castRingHom h) :=
  (injective_iff_map_eq_zero _).mpr λ x h1 ↦ match x with
    | O => rfl
    | I => h0.elim h1
    | X => h0.elim ((cast_mul h X Y).trans (mul_eq_zero_of_left h1 _))
    | Y => h0.elim ((cast_mul h Y X).trans (mul_eq_zero_of_left h1 _))
