/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Ring.Hom.Basic

/-!
# Explicit construction of 𝔽₂

In this file, we explicitly construct the field of 2 elements.
We prove just the necessary properties for the purpose of the main problem.
-/

namespace IMOSL
namespace IMO2012A5

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



protected theorem zero_add (x : 𝔽₂) : 0 + x = x := rfl

protected theorem add_zero : ∀ x : 𝔽₂, x + 0 = x
  | O => rfl
  | I => rfl

protected theorem add_comm : ∀ x y : 𝔽₂, x + y = y + x
  | O, x => x.add_zero.symm
  | I, O => rfl
  | I, I => rfl

protected theorem add_assoc : ∀ x y z : 𝔽₂, x + y + z = x + (y + z)
  | O, _, _ => rfl
  | I, O, _ => rfl
  | I, I, O => rfl
  | I, I, I => rfl

protected theorem add_left_neg : ∀ x : 𝔽₂, -x + x = 0
  | O => rfl
  | I => rfl

protected theorem zero_mul (x : 𝔽₂) : 0 * x = 0 := rfl

protected theorem mul_zero : ∀ x : 𝔽₂, x * 0 = 0
  | O => rfl
  | I => rfl

protected theorem one_mul (x : 𝔽₂) : 1 * x = x := rfl

protected theorem mul_one : ∀ x : 𝔽₂, x * 1 = x
  | O => rfl
  | I => rfl

protected theorem mul_comm : ∀ x y : 𝔽₂, x * y = y * x
  | I, x => x.mul_one.symm
  | O, O => rfl
  | O, I => rfl

protected theorem mul_assoc : ∀ x y z : 𝔽₂, x * y * z = x * (y * z)
  | O, _, _ => rfl
  | I, _, _ => rfl

protected theorem mul_add : ∀ x y z : 𝔽₂, x * (y + z) = x * y + x * z
  | O, _, _ => rfl
  | I, _, _ => rfl

protected theorem add_mul : ∀ x y z : 𝔽₂, (x + y) * z = x * z + y * z
  | O, _, _ => rfl
  | I, O, z => z.add_zero.symm
  | I, I, O => rfl
  | I, I, I => rfl

instance : CommRing 𝔽₂ :=
  { add_assoc := 𝔽₂.add_assoc
    zero_add := 𝔽₂.zero_add
    add_zero := 𝔽₂.add_zero
    add_comm := 𝔽₂.add_comm
    zero_mul := 𝔽₂.zero_mul
    mul_zero := 𝔽₂.mul_zero
    mul_assoc := 𝔽₂.mul_assoc
    one_mul := 𝔽₂.one_mul
    mul_one := 𝔽₂.mul_one
    add_left_neg := 𝔽₂.add_left_neg
    mul_comm := 𝔽₂.mul_comm
    left_distrib := 𝔽₂.mul_add
    right_distrib := 𝔽₂.add_mul }





/-! ## Homomorphism from `𝔽₂` -/

def cast {R : Type _} [AddGroupWithOne R] : 𝔽₂ → R
  | O => 0
  | I => 1


section Ring

variable {R : Type _} [Ring R]

theorem cast_eq_zero_imp (h : (1 : R) ≠ 0) :
    ∀ x : 𝔽₂, cast (R := R) x = 0 → x = 0
  | O => λ _ ↦ rfl
  | I => λ h0 ↦ absurd h0 h

theorem cast_mul : ∀ x y : 𝔽₂, cast (R := R) (x * y) = cast x * cast y
  | O, _ => (zero_mul _).symm
  | I, _ => (one_mul _).symm

variable (h : (2 : R) = 0)

theorem cast_add : ∀ x y : 𝔽₂, cast (R := R) (x + y) = cast x + cast y
  | O, _ => (zero_add _).symm
  | I, O => (add_zero 1).symm
  | I, I => (one_add_one_eq_two.trans h).symm

def castHom : 𝔽₂ →+* R :=
  { toFun := cast
    map_one' := rfl
    map_mul' := cast_mul
    map_zero' := rfl
    map_add' := cast_add h }

theorem castHom_injective (h0 : (1 : R) ≠ 0) : Function.Injective (castHom h) :=
  (injective_iff_map_eq_zero (castHom h)).mpr (cast_eq_zero_imp h0)

end Ring

end 𝔽₂
end IMO2012A5
end IMOSL
