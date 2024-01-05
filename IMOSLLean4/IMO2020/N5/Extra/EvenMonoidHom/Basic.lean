/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Hom.Basic

/-!
# "Even" homomorphism `M →* N`

Let `M` and `N` be a monoid, with `M` containing `-1`.
That is, `M` has a negation operator `- : M → M` such that
  `-(-x) = x` and `(-x)y = x(-y) = -(xy)` for all `x y : M`.
An even homomorphism `f : M →* N` is a homomorphism with `f(-1) = 1`.
If `M` is a commutative group, then the set of such homomorphism is
  isomorphic with `M⧸{±1} →* N`, but is easier to work with than `M⧸{±1} →* N`.
The isomorphism will be provided in `QuotEquiv.lean`.
-/

namespace IMOSL
namespace IMO2020N5

structure EvenMonoidHom (M : Type*) [MulOneClass M] [HasDistribNeg M]
    (N : Type*) [MulOneClass N] extends MonoidHom M N where
  protected map_neg_one' : toMonoidHom.toFun (-1) = 1





namespace EvenMonoidHom

/-! #### Basic properties -/
section MulOneClass

variable [MulOneClass M] [HasDistribNeg M] [MulOneClass N]

instance : CoeFun (EvenMonoidHom M N) (λ _ ↦ M → N) :=
  ⟨λ f ↦ f.toMonoidHom.toFun⟩

@[simp] lemma map_one (f : EvenMonoidHom M N) : f 1 = 1 :=
  f.map_one'

@[simp] lemma map_mul (f : EvenMonoidHom M N) (x y) : f (x * y) = f x * f y :=
  f.map_mul' x y

@[simp] lemma map_neg_one (f : EvenMonoidHom M N) : f (-1) = 1 :=
  f.map_neg_one'

@[simp] lemma map_neg (f : EvenMonoidHom M N) (x) : f (-x) = f x := by
  rw [← neg_one_mul, f.map_mul, f.map_neg_one, one_mul]

instance funLike (M : outParam Type*) [MulOneClass M] [HasDistribNeg M]
    (N : outParam Type*) [MulOneClass N] :
    FunLike (EvenMonoidHom M N) M (λ _ ↦ N) where
  coe f := f.toMonoidHom.toFun
  coe_injective' _ _ h := by rw [mk.injEq]; exact MonoidHom.ext (congrFun h)

theorem coe_inj {f g : EvenMonoidHom M N} : (f : M → N) = g ↔ f = g :=
  ⟨λ h ↦ FunLike.coe_injective' h, λ h ↦ h ▸ rfl⟩

@[ext] theorem ext {f g : EvenMonoidHom M N} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

theorem ext_iff {f g : EvenMonoidHom M N} : f = g ↔ ∀ x, f x = g x :=
  ⟨λ h _ ↦ h ▸ rfl, ext⟩


instance : One (EvenMonoidHom M N) where one :=
  { toMonoidHom := 1
    map_neg_one' := rfl }

@[simp] theorem one_apply : (1 : EvenMonoidHom M N) x = 1 := rfl

end MulOneClass



/-! #### Commutative monoid structure -/
section CommMonoid

variable [CommMonoid M] [HasDistribNeg M] [CommMonoid N]

instance : Mul (EvenMonoidHom M N) where mul := λ f g ↦
  { toMonoidHom := f.toMonoidHom * g.toMonoidHom
    map_neg_one' := one_mul (1 : N) ▸ congr_arg₂ _ f.map_neg_one g.map_neg_one }

@[simp] theorem mul_apply {f g : EvenMonoidHom M N} :
    (f * g) x = f x * g x := rfl

instance : CommMonoid (EvenMonoidHom M N) :=
  { mul_comm := λ _ _ ↦ ext λ _ ↦ mul_comm _ _
    mul_assoc := λ _ _ _ ↦ ext λ _ ↦ mul_assoc _ _ _
    one_mul := λ _ ↦ ext λ _ ↦ one_mul _
    mul_one := λ _ ↦ ext λ _ ↦ mul_one _ }

end CommMonoid
