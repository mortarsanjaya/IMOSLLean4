/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Mathlib.Algebra.CharP.Two

/-!
# Explicit construction of `𝔽₂`

In this file, we explicitly construct `𝔽₂`, the field of 2 elements.
We prove that it is a ring, and we construct ring homomorphisms from `𝔽₂`.

### TODO

Unify with `ZMod 2`.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

inductive 𝔽₂
  | O : 𝔽₂
  | I : 𝔽₂


namespace 𝔽₂

protected def add : 𝔽₂ → 𝔽₂ → 𝔽₂
  | O, x => x
  | I, O => I
  | I, I => O

protected def mul : 𝔽₂ → 𝔽₂ → 𝔽₂
  | O, _ => O
  | I, x => x

instance : Zero 𝔽₂ := ⟨O⟩
instance : One 𝔽₂ := ⟨I⟩
instance : Add 𝔽₂ := ⟨𝔽₂.add⟩
instance : Neg 𝔽₂ := ⟨id⟩
instance : Mul 𝔽₂ := ⟨𝔽₂.mul⟩

instance : DecidableEq 𝔽₂
  | O, O => isTrue rfl
  | O, I => isFalse noConfusion
  | I, O => isFalse noConfusion
  | I, I => isTrue rfl

instance : Fintype 𝔽₂ where
  elems := {O, I}
  complete x := by cases x <;> decide

/-- `𝔽₂[ε]` is a commutative group. -/
instance : AddCommGroup 𝔽₂ where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `𝔽₂[ε]` is a commutative ring. -/
instance : CommRing 𝔽₂ where
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  left_distrib := by decide
  right_distrib := by decide



/-! ### Ring homomorphism from `𝔽₂` -/

def cast [AddMonoidWithOne R] : 𝔽₂ → R
  | O => 0
  | I => 1


variable [NonAssocSemiring R] [CharP R 2]

theorem cast_add (x y) : cast (R := R) (x + y) = cast x + cast y := by
  match x, y with
  | O, _ => exact (zero_add _).symm
  | I, O => exact (add_zero 1).symm
  | I, I => exact (CharTwo.add_self_eq_zero (1 : R)).symm

omit [CharP R 2] in
theorem cast_mul (x y) : cast (R := R) (x * y) = cast x * cast y := by
  match x, y with
  | O, _ => exact (zero_mul _).symm
  | I, _ => exact (one_mul _).symm

def castRingHom : 𝔽₂ →+* R where
  toFun := cast
  map_one' := rfl
  map_mul' := cast_mul
  map_zero' := rfl
  map_add' := cast_add

theorem castRingHom_injective (h : (1 : R) ≠ 0) :
    Function.Injective (castRingHom : 𝔽₂ →+* R) :=
  (injective_iff_map_eq_zero _).mpr λ x h1 ↦ match x with | O => rfl | I => h.elim h1
