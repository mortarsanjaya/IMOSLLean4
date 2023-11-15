/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Ring.Hom.Basic

/-!
# Explicit construction of 𝔽₂[X]/⟨X²⟩

In this file, we explicitly construct the ring `𝔽₂[ε] := 𝔽₂[X]/⟨X²⟩`.
We prove just the necessary properties for the purpose of the main problem.
The explicit construction is used instead of the `dual_number` API for
  the purpose of avoiding the use of `algebra` instances.
-/

namespace IMOSL
namespace IMO2012A5

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



protected theorem add_zero : ∀ x : 𝔽₂ε, x + 0 = x
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

protected theorem zero_add (x : 𝔽₂ε) : 0 + x = x := rfl

protected theorem add_comm : ∀ x y : 𝔽₂ε, x + y = y + x
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

protected theorem add_assoc : ∀ x y z : 𝔽₂ε, x + y + z = x + (y + z)
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

protected theorem add_left_neg : ∀ x : 𝔽₂ε, -x + x = 0
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

protected theorem zero_mul (x : 𝔽₂ε) : 0 * x = 0 := rfl

protected theorem mul_zero : ∀ x : 𝔽₂ε, x * 0 = 0
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

protected theorem mul_one : ∀ x : 𝔽₂ε, x * 1 = x
  | O => rfl
  | I => rfl
  | X => rfl
  | Y => rfl

protected theorem one_mul (x : 𝔽₂ε) : 1 * x = x := rfl

protected theorem mul_comm : ∀ x y : 𝔽₂ε, x * y = y * x
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

protected theorem mul_assoc : ∀ x y z : 𝔽₂ε, x * y * z = x * (y * z)
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

protected theorem mul_add : ∀ x y z : 𝔽₂ε, x * (y + z) = x * y + x * z
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

protected theorem add_mul (x y z : 𝔽₂ε) : (x + y) * z = x * z + y * z :=
  by rw [𝔽₂ε.mul_comm, 𝔽₂ε.mul_add, z.mul_comm, z.mul_comm]

instance : CommRing 𝔽₂ε :=
  { add_assoc := 𝔽₂ε.add_assoc
    zero_add := 𝔽₂ε.zero_add
    add_zero := 𝔽₂ε.add_zero
    add_comm := 𝔽₂ε.add_comm
    zero_mul := 𝔽₂ε.zero_mul
    mul_zero := 𝔽₂ε.mul_zero
    mul_assoc := 𝔽₂ε.mul_assoc
    one_mul := 𝔽₂ε.one_mul
    mul_one := 𝔽₂ε.mul_one
    add_left_neg := 𝔽₂ε.add_left_neg
    mul_comm := 𝔽₂ε.mul_comm
    left_distrib := 𝔽₂ε.mul_add
    right_distrib := 𝔽₂ε.add_mul }





/-! ## Homomorphism from `𝔽₂ε` -/

def cast {R : Type _} [AddGroupWithOne R] (r : R) : 𝔽₂ε → R
  | O => 0
  | I => 1
  | X => r
  | Y => r + 1


section Ring

variable {R : Type _} [Ring R] (h : (2 : R) = 0)

theorem cast_add (r : R) (x y : 𝔽₂ε) : cast r (x + y) = cast r x + cast r y :=
  have h0 : (1 : R) + 1 = 0 := one_add_one_eq_two.trans h
  have h1 : r + r = 0 := by rw [← two_mul, h, zero_mul]
  match x, y with
    | O, _ => (zero_add _).symm
    | x, O => x.add_zero.symm ▸ (add_zero _).symm
    | I, I => h0.symm
    | I, X => add_comm r 1
    | I, Y => (self_eq_add_right.mpr h0).trans (add_left_comm r 1 1)
    | X, I => rfl
    | X, X => h1.symm
    | X, Y => (self_eq_add_left.mpr h1).trans (add_assoc r r 1)
    | Y, I => (self_eq_add_right.mpr h0).trans (add_assoc r 1 1).symm
    | Y, X => (self_eq_add_left.mpr h1).trans (add_right_comm r r 1)
    | Y, Y => (mul_eq_zero_of_left h (r + 1)).symm.trans (two_mul _)

variable {r : R} (h0 : r * r = 0)

theorem cast_mul : ∀ x y : 𝔽₂ε, cast r (x * y) = cast r x * cast r y
  | O, _ => (zero_mul _).symm
  | I, _ => (one_mul _).symm
  | x, I => x.mul_one.symm ▸ (mul_one _).symm
  | X, O => (mul_zero r).symm
  | X, X => h0.symm
  | X, Y => (add_left_eq_self.mpr h0).symm.trans (mul_add_one r r).symm
  | Y, O => (mul_zero (r + 1)).symm
  | Y, X => (add_left_eq_self.mpr h0).symm.trans (add_one_mul r r).symm
  | Y, Y => by change 1 = (r + 1) * (r + 1)
               rw [add_one_mul r, mul_add_one r, h0, zero_add,
                 ← add_assoc, ← two_mul, h, zero_mul, zero_add]

def castHom : 𝔽₂ε →+* R :=
  { toFun := cast r
    map_one' := rfl
    map_mul' := cast_mul h h0
    map_zero' := rfl
    map_add' := cast_add h r }

variable (h1 : (r : R) ≠ 0)

theorem castHom_eq_zero_imp (x : 𝔽₂ε) (h2 : castHom h h0 x = 0) : x = 0 :=
  have h3 : (1 : R) ≠ 0 := λ h3 ↦ h1 <| by rw [← one_mul r, h3, zero_mul]
  match x with
    | O => rfl
    | I => absurd h2 h3
    | X => absurd h2 h1
    | Y => by apply Not.elim h3
              rwa [eq_neg_of_add_eq_zero_left h2, neg_mul_neg, one_mul] at h0

theorem castHom_injective : Function.Injective (castHom h h0) :=
  (injective_iff_map_eq_zero (castHom h h0)).mpr (castHom_eq_zero_imp h h0 h1)

end Ring

end 𝔽₂ε
end IMO2012A5
end IMOSL
