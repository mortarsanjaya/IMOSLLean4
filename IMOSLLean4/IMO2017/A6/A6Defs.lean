/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.FunLike.Basic

/-!
# IMO 2017 A6 (P2, Definitions)

Let $R$ be a ring, $S$ be an abelian group, and $ι : R → S$ be a function.
Determine all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(ι(f(x)) ι(f(y))) + f(x + y) = f(xy). $$

This file defines the functional equation and prove the most basic properties.
We say that $f$ is
* *$ι$-good* if $f$ satisfies the above functional equation;
* *non-periodic $ι$-good* if $f$ is $ι$-good and has no non-zero period.

The $\text{id}$-good functions are characterized for a decent amount of subcases on $R$.
The file `IMOSLLean4/IMO2017/A6/A6.lean` collects all the main results.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Good functions -/

/-- Good function. -/
structure GoodFun [Add R] [Mul R] [Add S] (ι : S → R) where
  toFun : R → S
  good_def' : ∀ x y, toFun (ι (toFun x) * ι (toFun y)) + toFun (x + y) = toFun (x * y)

@[deprecated]
def good [Add R] [Mul R] [Add S] (ι : S → R) (f : R → S) :=
  ∃ f₀ : GoodFun ι, f₀.toFun = f

/-- Class of good functions; see mathlib's `DFunLike` design. -/
class GoodFunClass (F) [Add R] [Mul R] [Add S] (ι : S → R) [FunLike F R S] where
  good_def : ∀ (f : F) (x y : R), f (ι (f x) * ι (f y)) + f (x + y) = f (x * y)


namespace GoodFun

variable [Add R] [Mul R]

instance [Add S] (ι : S → R) : FunLike (GoodFun ι) R S where
  coe f := f.toFun
  coe_injective' f g h := by rwa [GoodFun.mk.injEq]

instance [Add S] (ι : S → R) : GoodFunClass (GoodFun ι) ι where
  good_def f := f.good_def'

@[ext] theorem ext [Add S] {ι : S → R} {f g : GoodFun ι} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

/-- The zero function as a good function. -/
protected def zero [AddZeroClass S] (ι : S → R) : GoodFun ι where
  toFun _ := 0
  good_def' _ _ := zero_add 0

instance [AddZeroClass S] (ι : S → R) : Zero (GoodFun ι) := ⟨GoodFun.zero ι⟩

end GoodFun


section

variable [Add R] [Mul R] [Add S] (ι : S → R) [FunLike F R S] [GoodFunClass F ι] (f : F)

/-- Coercion from `GoodFunClass` to `GoodFun`. -/
def GoodFunClass.toGoodFun : GoodFun ι where
  toFun := f
  good_def' := good_def f

theorem good_def : ∀ x y, f (ι (f x) * ι (f y)) + f (x + y) = f (x * y) :=
  GoodFunClass.good_def f

end


section

variable [NonUnitalNonAssocSemiring R] [Add S] (ι : S → R)
  [FunLike F R S] [GoodFunClass F ι] (f : F)

theorem map_map_zero_mul_map (x) : f (ι (f 0) * ι (f x)) + f x = f 0 := by
  have h := good_def ι f 0 x; rwa [zero_add, zero_mul] at h

theorem map_map_mul_map_zero (x) : f (ι (f x) * ι (f 0)) + f x = f 0 := by
  have h := good_def ι f x 0; rwa [add_zero, mul_zero] at h

end





/-! ### Non-periodic good functions -/

/-- Non-periodic good functions. -/
structure NonperiodicGoodFun [Add R] [Mul R] [Add S] (ι : S → R)
    extends GoodFun ι where
  period_imp_eq' (c d) (_ : ∀ x, toFun (x + c) = toFun (x + d)) : c = d

/-- Alternative constructor for non-periodic good functions. -/
def NonperiodicGoodFun.mk' [Add R] [Mul R] [Add S] (ι : S → R) (f : R → S)
    (good_def' : ∀ x y : R, f (ι (f x) * ι (f y)) + f (x + y) = f (x * y))
    (period_imp_eq' : ∀ c d, (∀ x, f (x + c) = f (x + d)) → c = d) :
    NonperiodicGoodFun ι :=
  ⟨⟨f, good_def'⟩, period_imp_eq'⟩

@[deprecated]
def nonperiodicGood [Add R] [Mul R] [Add S] (ι : S → R) (f : R → S) :=
  ∃ f₀ : NonperiodicGoodFun ι, f₀.toFun = f

/-- Class of non-periodic good functions; see mathlib's `DFunLike` design. -/
class NonperiodicGoodFunClass (F) [Add R] [Mul R] [Add S] (ι : S → R) [FunLike F R S]
    extends GoodFunClass F ι where
  period_imp_eq (f : F) (c d) (_ : ∀ x, f (x + c) = f (x + d)) : c = d



namespace NonperiodicGoodFun

variable [Add R] [Mul R] [Add S]

instance (ι : S → R) : FunLike (NonperiodicGoodFun ι) R S where
  coe f := f.toFun
  coe_injective' f g h := by rwa [NonperiodicGoodFun.mk.injEq, ← DFunLike.coe_fn_eq]

instance (ι : S → R) : NonperiodicGoodFunClass (NonperiodicGoodFun ι) ι where
  good_def f := f.good_def'
  period_imp_eq f := f.period_imp_eq'

@[ext] theorem ext {ι : S → R} {f g : NonperiodicGoodFun ι} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

end NonperiodicGoodFun


section

variable [Add R] [Mul R] [Add S] (ι : S → R) [FunLike F R S] [NonperiodicGoodFunClass F ι]
include ι

/-- Coercion from `NonperiodicGoodFunClass` to `NonperiodicGoodFun`. -/
def NonperiodicGoodFunClass.toNonperiodicGoodFun (f : F) : NonperiodicGoodFun ι :=
  { GoodFunClass.toGoodFun ι f with period_imp_eq' := period_imp_eq ι f }

theorem period_imp_eq {f : F} : (∀ x, f (x + c) = f (x + d)) → c = d :=
  NonperiodicGoodFunClass.period_imp_eq ι f _ _

theorem period_iff_eq {f : F} : (∀ x, f (x + c) = f (x + d)) ↔ c = d :=
  ⟨period_imp_eq ι, λ h _ ↦ by rw [h]⟩

end


section

variable [AddZeroClass R] [Mul R] [Add S] (ι : S → R)
  [FunLike F R S] [NonperiodicGoodFunClass F ι] {f : F}
include ι

theorem period_imp_zero (h : ∀ x, f (x + c) = f x) : c = 0 :=
  period_imp_eq ι (f := f) λ x ↦ by rw [h, add_zero]

theorem period_iff_zero : (∀ x, f (x + c) = f x) ↔ c = 0 :=
  ⟨period_imp_zero ι, λ h _ ↦ by rw [h, add_zero]⟩

end
