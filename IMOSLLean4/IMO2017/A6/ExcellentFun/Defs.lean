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


namespace ExcellentFun

variable [NonAssocRing R] [Add G]

instance : FunLike (ExcellentFun R G) R G where
  coe f := f.toFun
  coe_injective' f g h := by rwa [ExcellentFun.mk.injEq]

instance : ExcellentFunClass (ExcellentFun R G) R G where
  excellent_def f := f.excellent_def'

@[ext] theorem ext {f g : ExcellentFun R G} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

end ExcellentFun


section

variable [NonAssocRing R] [Add G] [FunLike F R G] [ExcellentFunClass F R G] (f : F)

/-- Coercion from `ExcellentFunClass` to `ExcellentFun`. -/
def ExcellentFunClass.toExcellentFun : ExcellentFun R G where
  toFun := f
  excellent_def' := excellent_def f

theorem excellent_def : ∀ x y, f (x + y - x * y) + f (1 - (x + y)) = f (1 - x * y) :=
  ExcellentFunClass.excellent_def f

end





/-! ### Some algebraic instances of excellent functions -/

namespace ExcellentFun

section

variable [NonAssocRing R] [AddZeroClass G]

/-- The zero function as a excellent function. -/
protected def zero : ExcellentFun R G where
  toFun _ := 0
  excellent_def' _ _ := zero_add 0

instance : Zero (ExcellentFun R G) := ⟨ExcellentFun.zero⟩

@[simp] theorem zero_apply (x) : (0 : ExcellentFun R G) x = 0 := rfl

end


section

variable [NonAssocRing R] [AddCommSemigroup G]

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

variable [NonAssocRing R] [AddCommMonoid G]

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


instance [NonAssocRing R] [AddCancelCommMonoid G] :
    AddCancelCommMonoid (ExcellentFun R G) where
  add_left_cancel _ _ _ h := ext λ x ↦ add_left_cancel (ExcellentFun.ext_iff.mp h x)


section

variable [NonAssocRing R] [SubtractionCommMonoid G]

protected def neg (f : ExcellentFun R G) : ExcellentFun R G where
  toFun x := -f x
  excellent_def' x y := by rw [← neg_add_rev, add_comm, excellent_def]

instance : Neg (ExcellentFun R G) := ⟨ExcellentFun.neg⟩

@[simp] theorem neg_apply (f : ExcellentFun R G) (x) : (-f) x = -f x := rfl

protected def sub (f g : ExcellentFun R G) : ExcellentFun R G := f + -g

instance : Sub (ExcellentFun R G) := ⟨ExcellentFun.sub⟩

@[simp] theorem sub_apply (f g : ExcellentFun R G) (x) : (f - g) x = f x - g x :=
  (sub_eq_add_neg (f x) (g x)).symm

end


instance [NonAssocRing R] [AddCommGroup G] : AddCommGroup (ExcellentFun R G) :=
  { ExcellentFun.instAddCommMonoid with
    neg_add_cancel := λ f ↦ ext λ x ↦ neg_add_cancel (f x)
    zsmul := zsmulRec }

end ExcellentFun
