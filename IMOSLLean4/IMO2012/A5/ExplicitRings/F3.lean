/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Ring.Hom.Basic

/-!
# Explicit construction of 𝔽₃

In this file, we explicitly construct the field of 3 elements.
We prove just the necessary properties for the purpose of the main problem.
-/

namespace IMOSL
namespace IMO2012A5

inductive 𝔽₃
  | 𝔽₃0 : 𝔽₃
  | 𝔽₃1 : 𝔽₃
  | 𝔽₃2 : 𝔽₃



namespace 𝔽₃

protected def add : 𝔽₃ → 𝔽₃ → 𝔽₃
  | 𝔽₃0, x => x
  | 𝔽₃1, 𝔽₃0 => 𝔽₃1
  | 𝔽₃1, 𝔽₃1 => 𝔽₃2
  | 𝔽₃1, 𝔽₃2 => 𝔽₃0
  | 𝔽₃2, 𝔽₃0 => 𝔽₃2
  | 𝔽₃2, 𝔽₃1 => 𝔽₃0
  | 𝔽₃2, 𝔽₃2 => 𝔽₃1

protected def neg : 𝔽₃ → 𝔽₃
  | 𝔽₃0 => 𝔽₃0
  | 𝔽₃1 => 𝔽₃2
  | 𝔽₃2 => 𝔽₃1

protected def mul : 𝔽₃ → 𝔽₃ → 𝔽₃
  | 𝔽₃0, _ => 𝔽₃0
  | 𝔽₃1, x => x
  | 𝔽₃2, 𝔽₃0 => 𝔽₃0
  | 𝔽₃2, 𝔽₃1 => 𝔽₃2
  | 𝔽₃2, 𝔽₃2 => 𝔽₃1

instance : Zero 𝔽₃ := ⟨𝔽₃0⟩
instance : One 𝔽₃ := ⟨𝔽₃1⟩
instance : Add 𝔽₃ := ⟨𝔽₃.add⟩
instance : Neg 𝔽₃ := ⟨𝔽₃.neg⟩
instance : Mul 𝔽₃ := ⟨𝔽₃.mul⟩



protected theorem add_zero : ∀ x : 𝔽₃, x + 0 = x
  | 𝔽₃0 => rfl
  | 𝔽₃1 => rfl
  | 𝔽₃2 => rfl

protected theorem zero_add (x : 𝔽₃) : 0 + x = x := rfl

protected theorem add_comm : ∀ x y : 𝔽₃, x + y = y + x
  | 𝔽₃0, x => x.add_zero.symm
  | x, 𝔽₃0 => x.add_zero
  | 𝔽₃1, 𝔽₃1 => rfl
  | 𝔽₃1, 𝔽₃2 => rfl
  | 𝔽₃2, 𝔽₃1 => rfl
  | 𝔽₃2, 𝔽₃2 => rfl

protected theorem add_assoc : ∀ x y z : 𝔽₃, x + y + z = x + (y + z)
  | 𝔽₃0, _, _ => rfl
  | x, 𝔽₃0, z => congr_arg (· + z) x.add_zero
  | x, y, 𝔽₃0 => y.add_zero.symm ▸ (x + y).add_zero
  | 𝔽₃1, 𝔽₃1, 𝔽₃1 => rfl
  | 𝔽₃1, 𝔽₃1, 𝔽₃2 => rfl
  | 𝔽₃1, 𝔽₃2, 𝔽₃1 => rfl
  | 𝔽₃1, 𝔽₃2, 𝔽₃2 => rfl
  | 𝔽₃2, 𝔽₃1, 𝔽₃1 => rfl
  | 𝔽₃2, 𝔽₃1, 𝔽₃2 => rfl
  | 𝔽₃2, 𝔽₃2, 𝔽₃1 => rfl
  | 𝔽₃2, 𝔽₃2, 𝔽₃2 => rfl

protected theorem add_left_neg : ∀ x : 𝔽₃, -x + x = 0
  | 𝔽₃0 => rfl
  | 𝔽₃1 => rfl
  | 𝔽₃2 => rfl

protected theorem zero_mul (x : 𝔽₃) : 0 * x = 0 := rfl

protected theorem mul_zero : ∀ x : 𝔽₃, x * 0 = 0
  | 𝔽₃0 => rfl
  | 𝔽₃1 => rfl
  | 𝔽₃2 => rfl

protected theorem mul_one : ∀ x : 𝔽₃, x * 1 = x
  | 𝔽₃0 => rfl
  | 𝔽₃1 => rfl
  | 𝔽₃2 => rfl

protected theorem one_mul (x : 𝔽₃) : 1 * x = x :=
  rfl

protected theorem mul_comm : ∀ x y : 𝔽₃, x * y = y * x
  | x, 𝔽₃1 => x.mul_one
  | 𝔽₃1, x => x.mul_one.symm
  | 𝔽₃0, 𝔽₃0 => rfl
  | 𝔽₃0, 𝔽₃2 => rfl
  | 𝔽₃2, 𝔽₃0 => rfl
  | 𝔽₃2, 𝔽₃2 => rfl

protected theorem mul_assoc : ∀ x y z : 𝔽₃, x * y * z = x * (y * z)
  | 𝔽₃0, _, _ => rfl
  | 𝔽₃1, _, _ => rfl
  | 𝔽₃2, 𝔽₃0, _ => rfl
  | 𝔽₃2, 𝔽₃1, _ => rfl
  | 𝔽₃2, 𝔽₃2, 𝔽₃0 => rfl
  | 𝔽₃2, 𝔽₃2, 𝔽₃1 => rfl
  | 𝔽₃2, 𝔽₃2, 𝔽₃2 => rfl

protected theorem mul_add : ∀ x y z : 𝔽₃, x * (y + z) = x * y + x * z
  | 𝔽₃0, _, _ => rfl
  | 𝔽₃1, _, _ => rfl
  | 𝔽₃2, 𝔽₃0, _ => rfl
  | 𝔽₃2, 𝔽₃1, 𝔽₃0 => rfl
  | 𝔽₃2, 𝔽₃1, 𝔽₃1 => rfl
  | 𝔽₃2, 𝔽₃1, 𝔽₃2 => rfl
  | 𝔽₃2, 𝔽₃2, 𝔽₃0 => rfl
  | 𝔽₃2, 𝔽₃2, 𝔽₃1 => rfl
  | 𝔽₃2, 𝔽₃2, 𝔽₃2 => rfl

protected theorem add_mul (x y z : 𝔽₃) : (x + y) * z = x * z + y * z :=
  by rw [𝔽₃.mul_comm, 𝔽₃.mul_add, z.mul_comm, z.mul_comm]

instance : CommRing 𝔽₃ :=
  { add_assoc := 𝔽₃.add_assoc
    zero_add := 𝔽₃.zero_add
    add_zero := 𝔽₃.add_zero
    add_comm := 𝔽₃.add_comm
    zero_mul := 𝔽₃.zero_mul
    mul_zero := 𝔽₃.mul_zero
    mul_assoc := 𝔽₃.mul_assoc
    one_mul := 𝔽₃.one_mul
    mul_one := 𝔽₃.mul_one
    add_left_neg := 𝔽₃.add_left_neg
    mul_comm := 𝔽₃.mul_comm
    left_distrib := 𝔽₃.mul_add
    right_distrib := 𝔽₃.add_mul }





/-! ## Homomorphism from `𝔽₃` -/

def cast [AddGroupWithOne R] : 𝔽₃ → R
  | 𝔽₃0 => 0
  | 𝔽₃1 => 1
  | 𝔽₃2 => -1


variable [Ring R]

theorem cast_eq_zero_imp (h : (1 : R) ≠ 0) :
    ∀ x : 𝔽₃, cast (R := R) x = 0 → x = 0
  | 𝔽₃0 => λ _ ↦ rfl
  | 𝔽₃1 => λ h0 ↦ absurd h0 h
  | 𝔽₃2 => λ h0 ↦ absurd (neg_eq_zero.mp h0) h

theorem cast_mul : ∀ x y : 𝔽₃, cast (R := R) (x * y) = cast x * cast y
  | 𝔽₃0, _ => (zero_mul _).symm
  | 𝔽₃1, _ => (one_mul _).symm
  | 𝔽₃2, 𝔽₃0 => (mul_zero (-1)).symm
  | 𝔽₃2, 𝔽₃1 => (mul_one (-1)).symm
  | 𝔽₃2, 𝔽₃2 => ((neg_mul_neg _ _).trans <| mul_one 1).symm

variable (h : (3 : R) = 0)

theorem cast_add (x y : 𝔽₃) : cast (R := R) (x + y) = cast x + cast y :=
  have h : (1 : R) + 1 = -1 :=
    by rwa [one_add_one_eq_two, eq_neg_iff_add_eq_zero, two_add_one_eq_three]
  match x, y with
    | 𝔽₃0, _ => (zero_add _).symm
    | x, 𝔽₃0 => x.add_zero.symm ▸ (add_zero _).symm
    | 𝔽₃1, 𝔽₃1 => h.symm
    | 𝔽₃1, 𝔽₃2 => (add_neg_self 1).symm
    | 𝔽₃2, 𝔽₃1 => (neg_add_self 1).symm
    | 𝔽₃2, 𝔽₃2 => (neg_eq_iff_eq_neg.mpr h).symm.trans (neg_add _ _)

def castHom : 𝔽₃ →+* R :=
  { toFun := cast
    map_one' := rfl
    map_mul' := cast_mul
    map_zero' := rfl
    map_add' := cast_add h }

theorem castHom_injective (h0 : (1 : R) ≠ 0) : Function.Injective (castHom h) :=
  (injective_iff_map_eq_zero (castHom h)).mpr (cast_eq_zero_imp h0)

end 𝔽₃
end IMO2012A5
end IMOSL
