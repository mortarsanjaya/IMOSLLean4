/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Explicit construction of `ℤ₄`

In this file, we explicitly construct the ring $ℤ/4ℤ$, (unfortunately) denoted `ℤ₄`.
We prove that it is a ring, and we construct ring homomorphisms from `ℤ₄`.
-/

namespace IMOSL
namespace IMO2012A5

inductive ℤ₄
  | ℤ₄0 : ℤ₄
  | ℤ₄1 : ℤ₄
  | ℤ₄2 : ℤ₄
  | ℤ₄3 : ℤ₄


namespace ℤ₄

protected def add : ℤ₄ → ℤ₄ → ℤ₄
  | ℤ₄0, x => x
  | ℤ₄1, ℤ₄0 => ℤ₄1
  | ℤ₄1, ℤ₄1 => ℤ₄2
  | ℤ₄1, ℤ₄2 => ℤ₄3
  | ℤ₄1, ℤ₄3 => ℤ₄0
  | ℤ₄2, ℤ₄0 => ℤ₄2
  | ℤ₄2, ℤ₄1 => ℤ₄3
  | ℤ₄2, ℤ₄2 => ℤ₄0
  | ℤ₄2, ℤ₄3 => ℤ₄1
  | ℤ₄3, ℤ₄0 => ℤ₄3
  | ℤ₄3, ℤ₄1 => ℤ₄0
  | ℤ₄3, ℤ₄2 => ℤ₄1
  | ℤ₄3, ℤ₄3 => ℤ₄2

protected def neg : ℤ₄ → ℤ₄
  | ℤ₄0 => ℤ₄0
  | ℤ₄1 => ℤ₄3
  | ℤ₄2 => ℤ₄2
  | ℤ₄3 => ℤ₄1

protected def mul : ℤ₄ → ℤ₄ → ℤ₄
  | ℤ₄0, _ => ℤ₄0
  | ℤ₄1, x => x
  | ℤ₄2, ℤ₄0 => ℤ₄0
  | ℤ₄2, ℤ₄1 => ℤ₄2
  | ℤ₄2, ℤ₄2 => ℤ₄0
  | ℤ₄2, ℤ₄3 => ℤ₄2
  | ℤ₄3, ℤ₄0 => ℤ₄0
  | ℤ₄3, ℤ₄1 => ℤ₄3
  | ℤ₄3, ℤ₄2 => ℤ₄2
  | ℤ₄3, ℤ₄3 => ℤ₄1

instance : Zero ℤ₄ := ⟨ℤ₄0⟩
instance : One ℤ₄ := ⟨ℤ₄1⟩
instance : Add ℤ₄ := ⟨ℤ₄.add⟩
instance : Neg ℤ₄ := ⟨ℤ₄.neg⟩
instance : Mul ℤ₄ := ⟨ℤ₄.mul⟩





/-! ### `ℤ₄` is a commutative group -/

protected theorem add_zero : ∀ x : ℤ₄, x + 0 = x
  | ℤ₄0 => rfl
  | ℤ₄1 => rfl
  | ℤ₄2 => rfl
  | ℤ₄3 => rfl

protected theorem zero_add (x : ℤ₄) : 0 + x = x := rfl

protected theorem add_comm : ∀ x y : ℤ₄, x + y = y + x
  | ℤ₄0, x => x.add_zero.symm
  | x, ℤ₄0 => x.add_zero
  | ℤ₄1, ℤ₄1 => rfl
  | ℤ₄1, ℤ₄2 => rfl
  | ℤ₄1, ℤ₄3 => rfl
  | ℤ₄2, ℤ₄1 => rfl
  | ℤ₄2, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄1 => rfl
  | ℤ₄3, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄3 => rfl

protected theorem add_assoc : ∀ x y z : ℤ₄, x + y + z = x + (y + z)
  | ℤ₄0, _, _ => rfl
  | x, ℤ₄0, z => congr_arg (· + z) x.add_zero
  | x, y, ℤ₄0 => y.add_zero.symm ▸ (x + y).add_zero
  | ℤ₄1, ℤ₄1, ℤ₄1 => rfl
  | ℤ₄1, ℤ₄1, ℤ₄2 => rfl
  | ℤ₄1, ℤ₄1, ℤ₄3 => rfl
  | ℤ₄1, ℤ₄2, ℤ₄1 => rfl
  | ℤ₄1, ℤ₄2, ℤ₄2 => rfl
  | ℤ₄1, ℤ₄2, ℤ₄3 => rfl
  | ℤ₄1, ℤ₄3, ℤ₄1 => rfl
  | ℤ₄1, ℤ₄3, ℤ₄2 => rfl
  | ℤ₄1, ℤ₄3, ℤ₄3 => rfl
  | ℤ₄2, ℤ₄1, ℤ₄1 => rfl
  | ℤ₄2, ℤ₄1, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄1, ℤ₄3 => rfl
  | ℤ₄2, ℤ₄2, ℤ₄1 => rfl
  | ℤ₄2, ℤ₄2, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄2, ℤ₄3 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄1 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄1, ℤ₄1 => rfl
  | ℤ₄3, ℤ₄1, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄1, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄1 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄1 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄3 => rfl

protected theorem neg_add_cancel : ∀ x : ℤ₄, -x + x = 0
  | ℤ₄0 => rfl
  | ℤ₄1 => rfl
  | ℤ₄2 => rfl
  | ℤ₄3 => rfl

instance : AddCommGroup ℤ₄ :=
  { add_assoc := ℤ₄.add_assoc
    zero_add := ℤ₄.zero_add
    add_zero := ℤ₄.add_zero
    add_comm := ℤ₄.add_comm
    neg_add_cancel := ℤ₄.neg_add_cancel
    nsmul := nsmulRec
    zsmul := zsmulRec }





/-! ### `ℤ₄` is a ring -/

protected theorem zero_mul (x : ℤ₄) : 0 * x = 0 := rfl

protected theorem mul_zero : ∀ x : ℤ₄, x * 0 = 0
  | ℤ₄0 => rfl
  | ℤ₄1 => rfl
  | ℤ₄2 => rfl
  | ℤ₄3 => rfl

protected theorem mul_one : ∀ x : ℤ₄, x * 1 = x
  | ℤ₄0 => rfl
  | ℤ₄1 => rfl
  | ℤ₄2 => rfl
  | ℤ₄3 => rfl

protected theorem one_mul (x : ℤ₄) : 1 * x = x := rfl

protected theorem mul_comm : ∀ x y : ℤ₄, x * y = y * x
  | ℤ₄1, x => x.mul_one.symm
  | x, ℤ₄1 => x.mul_one
  | ℤ₄0, ℤ₄0 => rfl
  | ℤ₄0, ℤ₄2 => rfl
  | ℤ₄0, ℤ₄3 => rfl
  | ℤ₄2, ℤ₄0 => rfl
  | ℤ₄2, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄0 => rfl
  | ℤ₄3, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄3 => rfl

protected theorem mul_assoc : ∀ x y z : ℤ₄, x * y * z = x * (y * z)
  | ℤ₄0, _, _ => rfl
  | ℤ₄1, _, _ => rfl
  | ℤ₄2, ℤ₄0, _ => rfl
  | ℤ₄2, ℤ₄1, _ => rfl
  | ℤ₄3, ℤ₄0, _ => rfl
  | ℤ₄3, ℤ₄1, _ => rfl
  | ℤ₄2, ℤ₄2, ℤ₄0 => rfl
  | ℤ₄2, ℤ₄2, ℤ₄1 => rfl
  | ℤ₄2, ℤ₄2, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄2, ℤ₄3 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄0 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄1 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄0 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄1 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄0 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄1 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄3 => rfl

protected theorem mul_add : ∀ x y z : ℤ₄, x * (y + z) = x * y + x * z
  | ℤ₄0, _, _ => rfl
  | ℤ₄1, _, _ => rfl
  | ℤ₄2, ℤ₄0, _ => rfl
  | ℤ₄2, ℤ₄1, ℤ₄0 => rfl
  | ℤ₄2, ℤ₄1, ℤ₄1 => rfl
  | ℤ₄2, ℤ₄1, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄1, ℤ₄3 => rfl
  | ℤ₄2, ℤ₄2, ℤ₄0 => rfl
  | ℤ₄2, ℤ₄2, ℤ₄1 => rfl
  | ℤ₄2, ℤ₄2, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄2, ℤ₄3 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄0 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄1 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄3, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄0, _ => rfl
  | ℤ₄3, ℤ₄1, ℤ₄0 => rfl
  | ℤ₄3, ℤ₄1, ℤ₄1 => rfl
  | ℤ₄3, ℤ₄1, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄1, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄0 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄1 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄2, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄0 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄1 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄3, ℤ₄3 => rfl

protected theorem add_mul (x y z : ℤ₄) : (x + y) * z = x * z + y * z :=
  by rw [ℤ₄.mul_comm, ℤ₄.mul_add, z.mul_comm, z.mul_comm]

instance : CommRing ℤ₄ :=
  { ℤ₄.instAddCommGroup with
    zero_mul := ℤ₄.zero_mul
    mul_zero := ℤ₄.mul_zero
    mul_assoc := ℤ₄.mul_assoc
    one_mul := ℤ₄.one_mul
    mul_one := ℤ₄.mul_one
    mul_comm := ℤ₄.mul_comm
    left_distrib := ℤ₄.mul_add
    right_distrib := ℤ₄.add_mul }





/-! ### Ring homomorphism from `ℤ₄` -/

def cast [AddGroupWithOne R] : ℤ₄ → R
  | ℤ₄0 => 0
  | ℤ₄1 => 1
  | ℤ₄2 => 2
  | ℤ₄3 => -1

variable [NonAssocRing R] (h : (4 : R) = 0)
include h

theorem cast_add (x y : ℤ₄) : cast (R := R) (x + y) = cast x + cast y :=
  have h : (2 : R) + 2 = 0 := by rw [← h, ← Nat.cast_two, ← Nat.cast_add]; rfl
  have h0 : (1 : R) + 1 = 2 := one_add_one_eq_two
  have h1 : (-1 : R) = 1 + 2 := by rwa [neg_eq_iff_add_eq_zero, ← add_assoc, h0]
  match x, y with
    | ℤ₄0, _ => (zero_add _).symm
    | x, ℤ₄0 => x.add_zero.symm ▸ (add_zero _).symm
    | ℤ₄1, ℤ₄1 => one_add_one_eq_two.symm
    | ℤ₄1, ℤ₄2 => h1
    | ℤ₄1, ℤ₄3 => (add_neg_cancel 1).symm
    | ℤ₄2, ℤ₄1 => h1.trans (add_comm _ _)
    | ℤ₄2, ℤ₄2 => h.symm
    | ℤ₄2, ℤ₄3 => eq_add_neg_of_add_eq h0
    | ℤ₄3, ℤ₄1 => (neg_add_cancel 1).symm
    | ℤ₄3, ℤ₄2 => eq_neg_add_of_add_eq h0
    | ℤ₄3, ℤ₄3 => eq_neg_add_of_add_eq h1.symm

theorem cast_mul (x y : ℤ₄) : cast (R := R) (x * y) = cast x * cast y :=
  have h0 : (2 : R) + 2 = 0 := by rw [← h, ← Nat.cast_two, ← Nat.cast_add]; rfl
  match x, y with
    | ℤ₄0, x => (zero_mul _).symm
    | ℤ₄1, x => (one_mul _).symm
    | x, ℤ₄1 => x.mul_one.symm ▸ (mul_one _).symm
    | ℤ₄2, ℤ₄0 => (mul_zero 2).symm
    | ℤ₄2, ℤ₄2 => ((two_mul _).trans h0).symm
    | ℤ₄2, ℤ₄3 => (eq_neg_of_add_eq_zero_left h0).trans (mul_neg_one 2).symm
    | ℤ₄3, ℤ₄0 => (mul_zero (-1)).symm
    | ℤ₄3, ℤ₄2 => (eq_neg_of_add_eq_zero_left h0).trans (neg_one_mul 2).symm
    | ℤ₄3, ℤ₄3 => (one_mul 1).symm.trans (neg_mul_neg 1 1).symm

def castRingHom : ℤ₄ →+* R :=
  { toFun := cast
    map_one' := rfl
    map_mul' := cast_mul h
    map_zero' := rfl
    map_add' := cast_add h }

theorem castRingHom_injective (h0 : (2 : R) ≠ 0) :
    Function.Injective (castRingHom h) :=
  have h1 : (1 : R) ≠ 0 := λ h1 ↦ h0 <| by rw [← one_mul (2 : R), h1, zero_mul]
  (injective_iff_map_eq_zero _).mpr λ x h2 ↦ match x with
    | ℤ₄0 => rfl
    | ℤ₄1 => absurd h2 h1
    | ℤ₄2 => absurd h2 h0
    | ℤ₄3 => absurd (neg_eq_zero.mp h2) h1
