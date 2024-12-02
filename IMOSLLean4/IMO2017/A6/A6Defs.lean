/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.FunLike.Basic

/-!
# IMO 2017 A6 (P2, Definitions)

Let $R$ be a ring.
Determine all functions $f : R → R$ such that, for any $x, y ∈ R$,
$$ f(f(x) f(y)) + f(x + y) = f(xy). $$

This file defines the functional equation and prove the most basic properties.
We say that $f$ is
* `good` if it satisfies the above functional equation;
* `NonperiodicGood` if in addition, $f$ has no non-zero period.

The `good` functions are characterized for a decent amount of subcases on $R$.
The file `IMOSLLean4/IMO2017/A6/A6.lean` collects all the main results.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Good functions -/

@[ext] structure GoodFun (R) [NonUnitalNonAssocSemiring R] where
  toFun : R → R
  good_def' : ∀ x y, toFun (toFun x * toFun y) + toFun (x + y) = toFun (x * y)

class GoodFunClass (F) (R : outParam Type*)
    [NonUnitalNonAssocSemiring R] [FunLike F R R] where
  good_def : ∀ (f : F) (x y : R), f (f x * f y) + f (x + y) = f (x * y)

@[deprecated]
abbrev good [NonUnitalNonAssocSemiring R] (f : R → R) := ∃ f₀ : GoodFun R, f = f₀.toFun


section

variable [NonUnitalNonAssocSemiring R] [FunLike F R R] [GoodFunClass F R]

def GoodFunClass.toGoodFun (f : F) : GoodFun R where
  toFun := f
  good_def' := good_def f

instance : FunLike (GoodFun R) R R where
  coe f := f.toFun
  coe_injective' := λ f g ↦ GoodFun.mk.injEq f.toFun _ g.toFun _ ▸ id

instance : GoodFunClass (GoodFun R) R where
  good_def f := f.good_def'

theorem good_def (f : F) : ∀ x y, f (f x * f y) + f (x + y) = f (x * y) :=
  GoodFunClass.good_def f

theorem good_map_map_zero_mul_map (f : F) (x) : f (f 0 * f x) + f x = f 0 := by
  have h := good_def f 0 x; rwa [zero_add, zero_mul] at h

theorem good_map_map_mul_map_zero (f : F) (x) : f (f x * f 0) + f x = f 0 := by
  have h := good_def f x 0; rwa [add_zero, mul_zero] at h

end


theorem good_map_map_zero_mul_self [NonUnitalNonAssocSemiring R] [IsCancelAdd R]
    [FunLike F R R] [GoodFunClass F R] (f : F) : f (f 0 * f 0) = 0 := by
  rw [← add_right_cancel_iff, good_map_map_zero_mul_map, zero_add]





/-! ### Non-periodic good functions -/

@[ext] structure NonperiodicGoodFun (R) [NonUnitalNonAssocSemiring R] extends GoodFun R where
  period_imp_eq' (c d) (_ : ∀ x, toFun (x + c) = toFun (x + d)) : c = d

def NonperiodicGoodFun.mk' [NonUnitalNonAssocSemiring R] (f : R → R)
    (good_def' : ∀ x y : R, f (f x * f y) + f (x + y) = f (x * y))
    (period_imp_eq' : ∀ c d, (∀ x, f (x + c) = f (x + d)) → c = d) : NonperiodicGoodFun R :=
  ⟨⟨f, good_def'⟩, period_imp_eq'⟩

class NonperiodicGoodFunClass (F) (R : outParam Type*)
    [NonUnitalNonAssocSemiring R] [FunLike F R R] extends GoodFunClass F R where
  period_imp_eq (f : F) (c d) (_ : ∀ x, f (x + c) = f (x + d)) : c = d

@[deprecated]
abbrev nonperiodicGood [NonUnitalNonAssocSemiring R] (f : R → R) :=
  ∃ f₀ : NonperiodicGoodFun R, f = f₀.toFun


section

variable [NonUnitalNonAssocSemiring R] [FunLike F R R] [NonperiodicGoodFunClass F R]

def NonperiodicGoodFunClass.toNonperiodicGoodFun (f : F) : NonperiodicGoodFun R :=
  { GoodFunClass.toGoodFun f with period_imp_eq' := period_imp_eq f }

instance : FunLike (NonperiodicGoodFun R) R R where
  coe f := f.toFun
  coe_injective' := λ f g h ↦ by rwa [NonperiodicGoodFun.mk.injEq, GoodFun.mk.injEq]

instance : NonperiodicGoodFunClass (NonperiodicGoodFun R) R where
  good_def f := f.good_def'
  period_imp_eq f := f.period_imp_eq'

theorem period_imp_eq {f : F} : (∀ x, f (x + c) = f (x + d)) → c = d :=
  NonperiodicGoodFunClass.period_imp_eq f _ _

theorem period_imp_zero {f : F} (h : ∀ x, f (x + c) = f x) : c = 0 :=
  period_imp_eq (f := f) λ x ↦ by rw [h, add_zero]

end
