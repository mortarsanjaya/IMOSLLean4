/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Hom.Defs
import IMOSLLean4.Extra.CharTwo.Ring

/-!
# Explicit construction of `𝔽₄`

In this file, we explicitly construct `𝔽₄`, the field of 4 elements.
We prove that it is a ring, and we construct ring homomorphisms from `𝔽₄`.
-/

namespace IMOSL
namespace IMO2012A5

open Extra

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





/-! ### `𝔽₄` is a commutative group -/

protected theorem add_zero : ∀ x : 𝔽₄, x + 0 = x
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

protected theorem zero_add (x : 𝔽₄) : 0 + x = x := rfl

protected theorem add_comm : ∀ x y : 𝔽₄, x + y = y + x
  | O, x => x.add_zero.symm
  | x, O => x.add_zero
  | I, I => rfl
  | I, X => rfl
  | I, Y => rfl
  | X, I => rfl
  | X, X => rfl
  | X, Y => rfl
  | Y, I => rfl
  | Y, X => rfl
  | Y, Y => rfl

protected theorem add_assoc : ∀ x y z : 𝔽₄, x + y + z = x + (y + z)
  | O, _, _ => rfl
  | x, O, z => congr_arg (· + z) x.add_zero
  | x, y, O => y.add_zero.symm ▸ (x + y).add_zero
  | I, I, I => rfl
  | I, I, X => rfl
  | I, I, Y => rfl
  | I, X, I => rfl
  | I, X, X => rfl
  | I, X, Y => rfl
  | I, Y, I => rfl
  | I, Y, X => rfl
  | I, Y, Y => rfl
  | X, I, I => rfl
  | X, I, X => rfl
  | X, I, Y => rfl
  | X, X, I => rfl
  | X, X, X => rfl
  | X, X, Y => rfl
  | X, Y, I => rfl
  | X, Y, X => rfl
  | X, Y, Y => rfl
  | Y, I, I => rfl
  | Y, I, X => rfl
  | Y, I, Y => rfl
  | Y, X, I => rfl
  | Y, X, X => rfl
  | Y, X, Y => rfl
  | Y, Y, I => rfl
  | Y, Y, X => rfl
  | Y, Y, Y => rfl

protected theorem neg_add_cancel : ∀ x : 𝔽₄, -x + x = 0
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

instance : AddCommGroup 𝔽₄ :=
  { add_assoc := 𝔽₄.add_assoc
    zero_add := 𝔽₄.zero_add
    add_zero := 𝔽₄.add_zero
    add_comm := 𝔽₄.add_comm
    neg_add_cancel := 𝔽₄.neg_add_cancel
    nsmul := nsmulRec
    zsmul := zsmulRec }

instance : CharTwo 𝔽₄ := ⟨neg_add_cancel⟩





/-! ### `𝔽₄` is a ring -/

protected theorem zero_mul (x : 𝔽₄) : 0 * x = 0 := rfl

protected theorem mul_zero : ∀ x : 𝔽₄, x * 0 = 0
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

protected theorem mul_one : ∀ x : 𝔽₄, x * 1 = x
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

protected theorem one_mul (x : 𝔽₄) : 1 * x = x := rfl

protected theorem mul_comm : ∀ x y : 𝔽₄, x * y = y * x
  | I, x => x.mul_one.symm
  | x, I => x.mul_one
  | O, O => rfl
  | O, X => rfl
  | O, Y => rfl
  | X, O => rfl
  | X, X => rfl
  | X, Y => rfl
  | Y, O => rfl
  | Y, X => rfl
  | Y, Y => rfl

protected theorem mul_assoc : ∀ x y z : 𝔽₄, x * y * z = x * (y * z)
  | O, _, _ => rfl
  | I, _, _ => rfl
  | X, O, _ => rfl
  | X, I, _ => rfl
  | Y, O, _ => rfl
  | Y, I, _ => rfl
  | X, X, O => rfl
  | X, X, I => rfl
  | X, X, X => rfl
  | X, X, Y => rfl
  | X, Y, O => rfl
  | X, Y, I => rfl
  | X, Y, X => rfl
  | X, Y, Y => rfl
  | Y, X, O => rfl
  | Y, X, I => rfl
  | Y, X, X => rfl
  | Y, X, Y => rfl
  | Y, Y, O => rfl
  | Y, Y, I => rfl
  | Y, Y, X => rfl
  | Y, Y, Y => rfl

protected theorem mul_add : ∀ x y z : 𝔽₄, x * (y + z) = x * y + x * z
  | O, _, _ => rfl
  | I, _, _ => rfl
  | X, O, _ => rfl
  | X, I, O => rfl
  | X, I, I => rfl
  | X, I, X => rfl
  | X, I, Y => rfl
  | X, X, O => rfl
  | X, X, I => rfl
  | X, X, X => rfl
  | X, X, Y => rfl
  | X, Y, O => rfl
  | X, Y, I => rfl
  | X, Y, X => rfl
  | X, Y, Y => rfl
  | Y, O, _ => rfl
  | Y, I, O => rfl
  | Y, I, I => rfl
  | Y, I, X => rfl
  | Y, I, Y => rfl
  | Y, X, O => rfl
  | Y, X, I => rfl
  | Y, X, X => rfl
  | Y, X, Y => rfl
  | Y, Y, O => rfl
  | Y, Y, I => rfl
  | Y, Y, X => rfl
  | Y, Y, Y => rfl

protected theorem add_mul (x y z : 𝔽₄) : (x + y) * z = x * z + y * z :=
  by rw [𝔽₄.mul_comm, 𝔽₄.mul_add, z.mul_comm, z.mul_comm]

instance : CommRing 𝔽₄ :=
  { 𝔽₄.instAddCommGroup with
    zero_mul := 𝔽₄.zero_mul
    mul_zero := 𝔽₄.mul_zero
    mul_assoc := 𝔽₄.mul_assoc
    one_mul := 𝔽₄.one_mul
    mul_one := 𝔽₄.mul_one
    mul_comm := 𝔽₄.mul_comm
    left_distrib := 𝔽₄.mul_add
    right_distrib := 𝔽₄.add_mul }





/-! ### Ring homomorphism from `𝔽₄` -/

open CharTwo

def cast [AddMonoidWithOne R] (r : R) : 𝔽₄ → R
  | O => 0
  | I => 1
  | X => r
  | Y => r + 1

variable [NonAssocSemiring R] [CharTwo R]

theorem cast_add (r : R) : ∀ x y : 𝔽₄, cast r (x + y) = cast r x + cast r y
  | O, _ => (zero_add _).symm
  | x, O => x.add_zero.symm ▸ (add_zero _).symm
  | I, I => (add_self_eq_zero _).symm
  | I, X => CharTwo.add_comm r 1
  | I, Y => (add_add_cancel_middle₁ 1 r).symm
  | X, I => rfl
  | X, X => (add_self_eq_zero _).symm
  | X, Y => (add_add_cancel_left _ _).symm
  | Y, I => (add_add_cancel_right _ _).symm
  | Y, X => (add_add_cancel_middle₂ _ _).symm
  | Y, Y => (add_self_eq_zero _).symm

variable {r : R} (h : r * r + r = 1)
include h

theorem cast_mul : ∀ x y : 𝔽₄, cast r (x * y) = cast r x * cast r y
  | O, _ => (zero_mul _).symm
  | I, _ => (one_mul _).symm
  | x, O => x.mul_zero.symm ▸ (mul_zero _).symm
  | x, I => x.mul_one.symm ▸ (mul_one _).symm
  | X, X => add_eq_iff_eq_add'''.mpr h.symm
  | X, Y => h.symm.trans (mul_add_one r r).symm
  | Y, X => h.symm.trans (add_one_mul r r).symm
  | Y, Y => (add_eq_iff_eq_add''.mp h).trans (add_one_mul_self r).symm

def castRingHom : 𝔽₄ →+* R :=
  { toFun := cast r
    map_one' := rfl
    map_mul' := cast_mul h
    map_zero' := rfl
    map_add' := cast_add r }

theorem castRingHom_injective (h0 : (1 : R) ≠ 0) :
    Function.Injective (castRingHom h) :=
  (injective_iff_map_eq_zero _).mpr λ x h1 ↦ match x with
    | O => rfl
    | I => Not.elim h0 h1
    | X => Not.elim h0 ((cast_mul h X Y).trans (mul_eq_zero_of_left h1 _))
    | Y => Not.elim h0 ((cast_mul h Y X).trans (mul_eq_zero_of_left h1 _))
