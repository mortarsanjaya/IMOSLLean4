/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.FunLike.Basic

/-!
# Excellent function

Let $R$ be a ring and $G$ be an abelian (additive) group.
We say that a function $f : R → G$ is *excellent* if for any $x, y ∈ R$,
$$ f(x + y - xy) + f(1 - (x + y)) = f(1 - xy). $$
In this file, we define excellent functions and prove their most basic properties.
-/

namespace IMOSL
namespace IMO2017A6

structure ExcellentFun (R G) [NonAssocRing R] [Add G] where
  toFun : R → G
  excellent_def' : ∀ x y, toFun (x + y - x * y) + toFun (1 - (x + y)) = toFun (1 - x * y)

/-- Class of excellent functions; see mathlib's `DFunLike` design. -/
class ExcellentFunClass (F R G) [NonAssocRing R] [Add G] [FunLike F R G] where
  excellent_def : ∀ (f : F) (x y : R), f (x + y - x * y) + f (1 - (x + y)) = f (1 - x * y)


variable [NonAssocRing R]


namespace ExcellentFun

variable [Add G]

instance : FunLike (ExcellentFun R G) R G where
  coe f := f.toFun
  coe_injective' f g h := by rwa [ExcellentFun.mk.injEq]

instance : ExcellentFunClass (ExcellentFun R G) R G where
  excellent_def f := f.excellent_def'

@[ext] theorem ext {f g : ExcellentFun R G} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

end ExcellentFun


section

variable [Add G] [FunLike F R G] [ExcellentFunClass F R G] (f : F)

/-- Coercion from `ExcellentFunClass` to `ExcellentFun`. -/
def ExcellentFunClass.toExcellentFun : ExcellentFun R G where
  toFun := f
  excellent_def' := excellent_def f

theorem excellent_def : ∀ x y, f (x + y - x * y) + f (1 - (x + y)) = f (1 - x * y) :=
  ExcellentFunClass.excellent_def f

end





/-! ### Some lemmas on excellent functions -/

section

variable [AddZeroClass G] [FunLike F R G] [ExcellentFunClass F R G] (f : F) (x : R)

lemma excellent_map_self_add_map_one_sub : f x + f (1 - x) = f 1 := by
  have h := excellent_def f 0 x
  rwa [zero_add, zero_mul, sub_eq_add_neg,
    sub_eq_add_neg 1 0, neg_zero, add_zero, add_zero] at h

lemma excellent_map_one_add : f (1 + x) = f 1 + f x := by
  have h := (excellent_def f 1 (-x)).symm
  rwa [one_mul, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add_rev,
    neg_neg, neg_add_cancel_right, add_neg_cancel_comm_assoc] at h

end


lemma excellent_map_nat_add [AddMonoid G] [FunLike F R G] [ExcellentFunClass F R G]
    (f : F) (x : R) (n : ℕ) : f (n + x) = n • f 1 + f x := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_add, zero_nsmul, zero_add]
  | succ n n_ih => rw [succ_nsmul', Nat.add_comm, Nat.cast_add,
      Nat.cast_one, add_assoc, excellent_map_one_add, n_ih, add_assoc]

lemma excellent_map_zero [AddZeroClass G] [IsCancelAdd G]
    [FunLike F R G] [ExcellentFunClass F R G] (f : F) : f 0 = 0 :=
  add_right_cancel (b := f (1 - 0)) <| calc
    _ = f (0 + 0 - 0 * 0) + f (1 - (0 + 0)) := by
      rw [add_zero, mul_zero, sub_eq_add_neg, sub_eq_add_neg, neg_zero, add_zero, add_zero]
    _ = 0 + f (1 - 0) := by rw [excellent_def, zero_add, zero_mul]


section

variable [AddCancelMonoid G] [FunLike F R G] [ExcellentFunClass F R G] (f : F)

lemma excellent_map_nat (n : ℕ) : f n = n • f 1 := by
  rw [← add_zero (n : R), excellent_map_nat_add, excellent_map_zero, add_zero]

lemma excellent_map_self_add_map_neg (x : R) : f x + f (-x) = 0 :=
  add_left_cancel (a := f 1) <| calc
    _ = f (1 + x) + f (-x) := by rw [excellent_map_one_add, add_assoc]
    _ = f (1 + x) + f (1 - (1 + x)) := by
      rw [sub_eq_add_neg, neg_add_rev, add_neg_cancel_comm_assoc]
    _ = f 1 + 0 := by rw [excellent_map_self_add_map_one_sub, add_zero]

lemma excellent_map_neg_add_map_self (x : R) : f (-x) + f x = 0 := by
  rw [← excellent_map_self_add_map_neg f (-x), neg_neg]

end


section

variable [AddCommMonoid G] [FunLike F R G] [ExcellentFunClass F R G] (f : F)

lemma excellent_map_add_one (x : R) : f (x + 1) = f x + f 1 := by
  rw [add_comm, excellent_map_one_add, add_comm]

lemma excellent_map_add_nat (x : R) (n : ℕ) : f (x + n) = f x + n • f 1 := by
  rw [add_comm, excellent_map_nat_add, add_comm]

end





/-! ### Some algebraic instances of excellent functions -/

namespace ExcellentFun

section

variable [AddZeroClass G]

/-- The zero function as a excellent function. -/
protected def zero : ExcellentFun R G where
  toFun _ := 0
  excellent_def' _ _ := zero_add 0

instance : Zero (ExcellentFun R G) := ⟨ExcellentFun.zero⟩

@[simp] theorem zero_apply (x) : (0 : ExcellentFun R G) x = 0 := rfl

end


section

variable [AddCommSemigroup G]

protected def add (f g : ExcellentFun R G) : ExcellentFun R G where
  toFun x := f x + g x
  excellent_def' x y := calc (f _ + g _) + (f _ + g _)
    _ = (f (x + y - x * y) + f (1 - (x + y))) + (g (x + y - x * y) + g (1 - (x + y))) := by
      rw [add_assoc, ← add_assoc (g _), add_comm (g _), add_assoc, ← add_assoc]
    _ = _ := congrArg₂ _ (f.excellent_def' x y) (g.excellent_def' x y)

instance : Add (ExcellentFun R G) := ⟨ExcellentFun.add⟩

@[simp] theorem add_apply (f g : ExcellentFun R G) (x) : (f + g) x = f x + g x := rfl

instance : AddCommSemigroup (ExcellentFun R G) where
  add_assoc f₁ f₂ f₃ := ext λ x ↦ add_assoc (f₁ x) (f₂ x) (f₃ x)
  add_comm f g := ext λ x ↦ add_comm (f x) (g x)

end


section

variable [AddCommMonoid G]

instance : AddCommMonoid (ExcellentFun R G) :=
  { ExcellentFun.instAddCommSemigroup with
    zero_add := λ f ↦ ext λ x ↦ zero_add (f x)
    add_zero := λ f ↦ ext λ x ↦ add_zero (f x)
    nsmul := nsmulRec }

@[simp] theorem nsmul_apply (f : ExcellentFun R G) (n : ℕ) (x) : (n • f) x = n • f x := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, zero_apply]
  | succ n n_ih => rw [succ_nsmul, succ_nsmul, add_apply, n_ih]

end


section

variable [AddCancelCommMonoid G]

protected def neg (f : ExcellentFun R G) : ExcellentFun R G where
  toFun x := f (-x)
  excellent_def' x y := add_right_cancel (b := f (1 - x * y)) <|
    calc f (-(x + y - x * y)) + f (-(1 - (x + y))) + f (1 - x * y)
    _ = f (-_) + f (-_) + (f (1 - (x + y)) + f (x + y - x * y)) := by
      rw [← excellent_def, add_comm (f (1 - _))]
    _ = f (-(x + y - x * y)) + ((f (-(1 - (x + y))) + f (1 - (x + y))) + f _) := by
      rw [add_assoc, ← add_assoc (f (-(1 - (x + y))))]
    _ = 0 := by rw [excellent_map_neg_add_map_self, zero_add, excellent_map_neg_add_map_self]
    _ = f (-(1 - x * y)) + f (1 - x * y) := by rw [excellent_map_neg_add_map_self]

instance : Neg (ExcellentFun R G) := ⟨ExcellentFun.neg⟩

@[simp] theorem neg_apply (f : ExcellentFun R G) (x) : (-f) x = f (-x) := rfl

protected def sub (f g : ExcellentFun R G) : ExcellentFun R G := f + -g

instance : Sub (ExcellentFun R G) := ⟨ExcellentFun.sub⟩

@[simp] theorem sub_apply (f g : ExcellentFun R G) (x) : (f - g) x = f x + g (-x) := rfl

instance : AddCommGroup (ExcellentFun R G) :=
  { ExcellentFun.instAddCommMonoid with
    neg_add_cancel := λ f ↦ ext (excellent_map_neg_add_map_self f)
    zsmul := zsmulRec }

end

end ExcellentFun
