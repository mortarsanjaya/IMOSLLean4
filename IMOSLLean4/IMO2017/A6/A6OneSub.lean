/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Defs
import Mathlib.Algebra.Group.Basic

/-!
# IMO 2017 A6 (P2, The map `x ↦ 1 - x`)

We prove that the map `x ↦ 1 - x` is reduced $\text{id}_R$-good over any ring $R$.
-/

namespace IMOSL
namespace IMO2017A6

variable (R) [NonAssocRing R]

/-- The map `x ↦ 1 - x` as an `id_R`-good function. -/
def GoodFun_one_sub : GoodFun (id : R → R) where
  toFun := λ x ↦ 1 - x
  good_def' := λ x y ↦ calc 1 - (1 - x) * (1 - y) + (1 - (x + y))
    _ = 1 - (1 - (x + y - x * y)) + (1 - (x + y)) := by
      rw [mul_one_sub, one_sub_mul, sub_sub, ← add_sub_assoc x]
    _ = 1 - x * y := by rw [sub_sub_cancel, sub_add_sub_cancel']

/-- The map `x ↦ 1 - x` as a non-periodic `id_R`-good function. -/
def NonperiodicGoodFun_one_sub : NonperiodicGoodFun (id : R → R) :=
  { GoodFun_one_sub R with
    period_imp_eq' := λ _ _ h ↦ add_right_injective 0 (sub_right_injective (h 0)) }

/-- The map `x ↦ 1 - x` as a reduced `id_R`-good function. -/
def ReducedGoodFun_one_sub : ReducedGoodFun (id : R → R) :=
  {  NonperiodicGoodFun_one_sub R with map_zero_eq_one' := sub_zero 1 }
