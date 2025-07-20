/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.FunLike.Basic

/-!
# IMO 2017 A6 (P2, Definitions)

Let $R$ be a ring, $G$ be an abelian group, and $ι : R → G$ be a group homomorphism.
Determine all functions $f : R → G$ such that, for any $x, y ∈ R$,
$$ f(ι(f(x)) ι(f(y))) + f(x + y) = f(xy). $$

We say that $f$ is
* *$ι$-good* if $f$ satisfies the above functional equation;
* *non-periodic $ι$-good* if $f$ is $ι$-good and has no non-zero period.

This file defines the functional equation and prove basic properties.
The good functions are characterized for a decent amount of subcases.
The file `IMOSLLean4/IMO2017/A6/A6.lean` collects all the main results.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Good functions -/

section

variable [Add R] [Mul R] [Add G]

/-- Good function. -/
structure GoodFun (ι : G → R) where
  toFun : R → G
  good_def' x y : toFun (ι (toFun x) * ι (toFun y)) + toFun (x + y) = toFun (x * y)

/-- Unbundled good function. -/
structure IsGoodFun (ι : G → R) (f : R → G) : Prop where
  good_def x y : f (ι (f x) * ι (f y)) + f (x + y) = f (x * y)

/-- Class of good functions; see mathlib's `DFunLike` design. -/
class GoodFunClass (F) (ι : outParam (G → R)) [FunLike F R G] where
  good_def : ∀ (f : F) (x y : R), f (ι (f x) * ι (f y)) + f (x + y) = f (x * y)


namespace GoodFun

instance (ι : G → R) : FunLike (GoodFun ι) R G where
  coe f := f.toFun
  coe_injective' f g h := by rwa [GoodFun.mk.injEq]

instance (ι : G → R) : GoodFunClass (GoodFun ι) ι where
  good_def f := f.good_def'

@[ext] theorem ext {ι : G → R} {f g : GoodFun ι} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

theorem IsGoodFun {ι : G → R} (f : GoodFun ι) : IsGoodFun ι f :=
  ⟨f.good_def'⟩

instance {G} [AddZeroClass G] (ι : G → R) : Zero (GoodFun ι) :=
  ⟨⟨λ _ ↦ 0, λ _ _ ↦ zero_add 0⟩⟩

theorem zero_apply {G} [AddZeroClass G] (ι : G → R) (x) : (0 : GoodFun ι) x = 0 := rfl

end GoodFun


namespace IsGoodFun

variable {ι : G → R} {f : R → G}

def toGoodFun (h : IsGoodFun ι f) : GoodFun ι where
  toFun := f
  good_def' := h.good_def

theorem toGoodFun_eq (h : IsGoodFun ι f) : h.toGoodFun = f := rfl

theorem iff : IsGoodFun ι f ↔ ∃ g : GoodFun ι, g = f :=
  ⟨λ h ↦ ⟨h.toGoodFun, rfl⟩, λ ⟨g, hg⟩ ↦ hg ▸ g.IsGoodFun⟩

theorem zero {G} [AddZeroClass G] {ι : G → R} : IsGoodFun ι (λ _ ↦ 0) :=
  ⟨λ _ _ ↦ zero_add 0⟩

end IsGoodFun


variable (ι : G → R) [FunLike F R G] [GoodFunClass F ι]

/-- Coercion from `GoodFunClass` to `GoodFun`. -/
def GoodFunClass.toGoodFun (f : F) : GoodFun ι where
  toFun := f
  good_def' := good_def f

theorem good_def (f : F) : ∀ x y, f (ι (f x) * ι (f y)) + f (x + y) = f (x * y) :=
  GoodFunClass.good_def f

end





/-! ### Non-periodic good functions -/

section

variable [Add R] [Mul R] [Add G]

/-- Non-periodic good functions. -/
structure NonperiodicGoodFun (ι : G → R) extends GoodFun ι where
  period_imp_eq' (c d) (_ : ∀ x, toFun (x + c) = toFun (x + d)) : c = d

/-- Unbundled good function. -/
structure IsNonperiodicGoodFun (ι : G → R) (f : R → G) extends IsGoodFun ι f where
  period_imp_eq {c d} (_ : ∀ x, f (x + c) = f (x + d)) : c = d

/-- Class of non-periodic good functions; see mathlib's `DFunLike` design. -/
class NonperiodicGoodFunClass (F) (ι : outParam (G → R)) [FunLike F R G]
    extends GoodFunClass F ι where
  period_imp_eq (f : F) (c d) (_ : ∀ x, f (x + c) = f (x + d)) : c = d


namespace NonperiodicGoodFun

instance (ι : G → R) : FunLike (NonperiodicGoodFun ι) R G where
  coe f := f.toFun
  coe_injective' f g h := by rwa [NonperiodicGoodFun.mk.injEq, ← DFunLike.coe_fn_eq]

instance (ι : G → R) : NonperiodicGoodFunClass (NonperiodicGoodFun ι) ι where
  good_def f := f.good_def'
  period_imp_eq f := f.period_imp_eq'

@[ext] theorem ext {ι : G → R} {f g : NonperiodicGoodFun ι} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

theorem IsNonperiodicGoodFun {ι : G → R} (f : NonperiodicGoodFun ι) :
    IsNonperiodicGoodFun ι f :=
  ⟨f.IsGoodFun, f.period_imp_eq' _ _⟩

instance [Subsingleton R] {G} [AddZeroClass G] (ι : G → R) : Zero (NonperiodicGoodFun ι) :=
  ⟨0, λ _ _ _ ↦ Subsingleton.allEq _ _⟩

theorem zero_apply [Subsingleton R] {G} [AddZeroClass G] (ι : G → R) (x) :
    (0 : NonperiodicGoodFun ι) x = 0 := rfl

end NonperiodicGoodFun


namespace IsNonperiodicGoodFun

variable {ι : G → R} {f : R → G}

def toNonperiodicGoodFun (h : IsNonperiodicGoodFun ι f) : NonperiodicGoodFun ι :=
  { h.toGoodFun with period_imp_eq' _ _ := h.period_imp_eq }

theorem toNonperiodicGoodFun_eq (h : IsNonperiodicGoodFun ι f) :
    h.toNonperiodicGoodFun = f := rfl

theorem iff : IsNonperiodicGoodFun ι f ↔ ∃ g : NonperiodicGoodFun ι, g = f :=
  ⟨λ h ↦ ⟨h.toNonperiodicGoodFun, rfl⟩, λ ⟨g, hg⟩ ↦ hg ▸ g.IsNonperiodicGoodFun⟩

theorem zero [Subsingleton R] {G} [AddZeroClass G] {ι : G → R} :
    IsNonperiodicGoodFun ι (λ _ ↦ 0) :=
  NonperiodicGoodFun.IsNonperiodicGoodFun 0

end IsNonperiodicGoodFun


variable (ι : G → R) [FunLike F R G] [NonperiodicGoodFunClass F ι]
include ι

/-- Coercion from `NonperiodicGoodFunClass` to `NonperiodicGoodFun`. -/
def NonperiodicGoodFunClass.toNonperiodicGoodFun (f : F) : NonperiodicGoodFun ι :=
  { GoodFunClass.toGoodFun ι f with period_imp_eq' := period_imp_eq f }

theorem period_imp_eq {f : F} : (∀ x, f (x + c) = f (x + d)) → c = d :=
  NonperiodicGoodFunClass.period_imp_eq f _ _

theorem period_iff_eq {f : F} : (∀ x, f (x + c) = f (x + d)) ↔ c = d :=
  ⟨period_imp_eq ι, λ h _ ↦ by rw [h]⟩

end


section

variable [AddZeroClass R] [Mul R] [Add G] (ι : G → R)
  [FunLike F R G] [NonperiodicGoodFunClass F ι] {f : F}
include ι

theorem period_imp_zero (h : ∀ x, f (x + c) = f x) : c = 0 :=
  period_imp_eq ι (f := f) λ x ↦ by rw [h, add_zero]

theorem period_iff_zero : (∀ x, f (x + c) = f x) ↔ c = 0 :=
  ⟨period_imp_zero ι, λ h _ ↦ by rw [h, add_zero]⟩

end





/-! ### Properties of good functions involving equality of values of `f` -/

section

variable [Add R] [Mul R] [Add G] (ι : G → R) [FunLike F R G] [GoodFunClass F ι]
include ι

lemma map_mul_eq_of_map_eq_of_map_add_eq
    {f : F} (h : f a = f b) (h0 : f c = f d) (h1 : f (a + c) = f (b + d)) :
    f (a * c) = f (b * d) := by
  rw [← good_def ι, h, h0, h1, good_def]

lemma map_mul_left_eq_of_map_add_left_eq
    {f : F} (h : f a = f b) (h0 : f (c + a) = f (c + b)) :
    f (c * a) = f (c * b) :=
  map_mul_eq_of_map_eq_of_map_add_eq ι rfl h h0

lemma map_mul_right_eq_of_map_add_right_eq
    {f : F} (h : f a = f b) (h0 : f (a + c) = f (b + c)) :
    f (a * c) = f (b * c) :=
  map_mul_eq_of_map_eq_of_map_add_eq ι h rfl h0

end


section

variable [Add R] [Mul R] [Add G] [IsCancelAdd G] (ι : G → R)
  [FunLike F R G] [GoodFunClass F ι] {f : F} (h : f a = f b)
include ι h

lemma map_add_eq_iff_map_mul_eq (h0 : f c = f d) :
    f (a + c) = f (b + d) ↔ f (a * c) = f (b * d) := by
  rw [← good_def ι, h, h0, ← good_def ι f b, add_left_cancel_iff]

lemma map_add_right_eq_iff_map_mul_right_eq :
    f (a + c) = f (b + c) ↔ f (a * c) = f (b * c) :=
  map_add_eq_iff_map_mul_eq ι h rfl

lemma map_add_left_eq_iff_map_mul_left_eq :
    f (c + a) = f (c + b) ↔ f (c * a) = f (c * b) :=
  map_add_eq_iff_map_mul_eq ι rfl h

end
