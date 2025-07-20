/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2017.A6.ExcellentFun.AddMonoidHom
import IMOSLLean4.Main.IMO2017.A6.ExcellentFun.Basic

/-! # `IsOfAddMonoidHomSurjective R G` instance if `G` is {2, 3}-torsion-free -/

namespace IMOSL
namespace IMO2017A6
namespace ExcellentFun

theorem IsOfAddMonoidHomSurjective_of_TwoThreeTorsionFree
    [NonAssocRing R] [AddCancelCommMonoid G]
    (hG2 : ∀ x y : G, 2 • x = 2 • y → x = y)
    (hG3 : ∀ x y : G, 3 • x = 3 • y → x = y) :
    IsOfAddMonoidHomSurjective R G := by
  refine IsOfAddMonoidHomSurjective.mk' λ f x y ↦ ?_
  have h := hG2 _ _ (excellent_linear_formula f x (3 * y))
  rw [← mul_add, ← Nat.cast_ofNat, excellent_map_nat_mul,
    excellent_map_nat_mul, ← nsmul_add] at h
  exact hG3 _ _ h
