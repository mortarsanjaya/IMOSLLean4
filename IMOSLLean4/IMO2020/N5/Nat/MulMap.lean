/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.FunLike.Basic

/-!
# Multiplicative Map

Let `M` be a commutative (multiplicative) monoid.
A multiplicative map is a map `f : ℕ → M` such that
  `f(0) = f(1) = 1` and `f(xy) = f(x) f(y)` for any `x, y > 0`.
The multiplicative maps form a monoid under pointwise multiplication.
We also prove other properties for multiplicative maps.
-/

namespace IMOSL
namespace IMO2020N5

/-- The main structure used to define the generalized IMO 2020 N5. -/
structure MulMap (M : Type*) [One M] [Mul M] :=
  toFun : ℕ → M
  map_zero' : toFun 0 = 1
  map_one' : toFun 1 = 1
  map_mul' : ∀ {x y}, 0 < x → 0 < y → toFun (x * y) = toFun x * toFun y





namespace MulMap

/-! #### Basic properties -/
section Mul

variable [One M] [Mul M]

instance : CoeFun (MulMap M) (λ _ ↦ ℕ → M) := ⟨MulMap.toFun⟩

@[simp] theorem map_zero (f : MulMap M) : f 0 = 1 := f.map_zero'
@[simp] theorem map_one (f : MulMap M) : f 1 = 1 := f.map_one'
@[simp] theorem map_mul (f : MulMap M) (h : 0 < x) (h0 : 0 < y) :
    f (x * y) = f x * f y :=
  f.map_mul' h h0

instance funLike (M : outParam Type*) [One M] [Mul M] :
    FunLike (MulMap M) ℕ (λ _ ↦ M) where
  coe f := f.toFun
  coe_injective' _ _ h := by rw [mk.injEq]; exact h

theorem coe_inj {f g : MulMap M} : (f : ℕ → M) = g ↔ f = g :=
  ⟨λ h ↦ FunLike.coe_injective' h, congr_arg toFun⟩

@[ext] theorem ext {f g : MulMap M} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

theorem ext_iff {f g : MulMap M} : f = g ↔ ∀ x, f x = g x :=
  ⟨λ h _ ↦ h ▸ rfl, ext⟩

end Mul



/-! #### Commutative monoid -/
section CommMonoid

instance [MulOneClass M] : One (MulMap M) where one :=
  { toFun := λ _ ↦ 1
    map_zero' := rfl
    map_one' := rfl
    map_mul' := λ _ _ ↦ (mul_one 1).symm }

@[simp] theorem one_apply [MulOneClass M] : (1 : MulMap M) x = 1 := rfl

variable [CommMonoid M]

instance : Mul (MulMap M) where mul := λ f g ↦
  { toFun := λ n ↦ f n * g n
    map_zero' := (congr_arg₂ _ f.map_zero g.map_zero).trans (mul_one _)
    map_one' := (congr_arg₂ _ f.map_one g.map_one).trans (mul_one _)
    map_mul' := λ h h0 ↦ (mul_mul_mul_comm (f _) _ _ _).symm ▸
      congr_arg₂ _ (f.map_mul h h0) (g.map_mul h h0) }

@[simp] theorem mul_apply {f g : MulMap M} : (f * g) n = f n * g n := rfl

instance : CommMonoid (MulMap M) :=
  { mul_comm := λ _ _ ↦ ext λ _ ↦ mul_comm _ _
    mul_assoc := λ _ _ _ ↦ ext λ _ ↦ mul_assoc _ _ _
    one_mul := λ _ ↦ ext λ _ ↦ one_mul _
    mul_one := λ _ ↦ ext λ _ ↦ mul_one _ }

end CommMonoid
