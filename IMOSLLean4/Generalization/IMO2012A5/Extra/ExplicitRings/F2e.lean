/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Mathlib.Algebra.CharP.Two

/-!
# Explicit construction of `𝔽₂ε`

In this file, we explicitly construct the ring $𝔽₂[X]/⟨X²⟩$, denoted `𝔽₂ε`.
We prove that it is a ring, and we construct ring homomorphisms from `𝔽₂ε`.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

inductive 𝔽₂ε
  | O : 𝔽₂ε
  | I : 𝔽₂ε
  | X : 𝔽₂ε
  | Y : 𝔽₂ε


namespace 𝔽₂ε

protected def add : 𝔽₂ε → 𝔽₂ε → 𝔽₂ε
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

protected def mul : 𝔽₂ε → 𝔽₂ε → 𝔽₂ε
  | O, _ => O
  | I, x => x
  | X, O => O
  | X, I => X
  | X, X => O
  | X, Y => X
  | Y, O => O
  | Y, I => Y
  | Y, X => X
  | Y, Y => I

instance : Zero 𝔽₂ε := ⟨O⟩
instance : One 𝔽₂ε := ⟨I⟩
instance : Add 𝔽₂ε := ⟨𝔽₂ε.add⟩
instance : Neg 𝔽₂ε := ⟨id⟩
instance : Mul 𝔽₂ε := ⟨𝔽₂ε.mul⟩

instance : DecidableEq 𝔽₂ε
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

instance : Fintype 𝔽₂ε where
  elems := {O, I, X, Y}
  complete x := by cases x <;> decide

/-- `𝔽₂[ε]` is a commutative group. -/
instance : AddCommGroup 𝔽₂ε where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `𝔽₂[ε]` is a commutative ring. -/
instance : CommRing 𝔽₂ε where
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  left_distrib := by decide
  right_distrib := by decide



/-! ## Ring homomorphism from `𝔽₂[ε]` -/

def cast [AddMonoidWithOne R] (r : R) : 𝔽₂ε → R
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

variable {r : R} (h : r * r = 0)
include h

theorem cast_mul (x y) : cast r (x * y) = cast r x * cast r y := by
  match x, y with
  | O, _ => exact (zero_mul _).symm
  | I, _ => exact (one_mul _).symm
  | X, O => exact (mul_zero _).symm
  | X, I => exact (mul_one _).symm
  | X, X => exact h.symm
  | X, Y => change r = r * (r + 1); rw [mul_add_one, h, zero_add]
  | Y, O => exact (mul_zero _).symm
  | Y, I => exact (mul_one _).symm
  | Y, X => change r = (r + 1) * r; rw [add_one_mul, h, zero_add]
  | Y, Y => change 1 = (r + 1) * (r + 1)
            rw [add_one_mul, mul_add_one, h, zero_add, CharTwo.add_cancel_left]

def castRingHom : 𝔽₂ε →+* R where
  toFun := cast r
  map_one' := rfl
  map_mul' := cast_mul h
  map_zero' := rfl
  map_add' := cast_add r

theorem castRingHom_injective (h0 : (r : R) ≠ 0) : Function.Injective (castRingHom h) :=
  (injective_iff_map_eq_zero _).mpr λ x h2 ↦ match x with
    | O => rfl
    | I => h0.elim (eq_zero_of_zero_eq_one h2.symm r)
    | X => h0.elim h2
    | Y => h0.elim ((cast_mul h Y X).trans (mul_eq_zero_of_left h2 _))
