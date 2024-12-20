/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6NonperiodicSol
import IMOSLLean4.IMO2017.A6.ExcellentFun.Basic
import IMOSLLean4.IMO2017.A6.Extra.TorsionFreeBy

/-!
# IMO 2017 A6 (P2, Classifying good functions: 2- and 3-torsion-free case)

We solve the problem when `G` is `2`-torsion free and `3`-torsion free.
-/

namespace IMOSL
namespace IMO2017A6

open Extra

instance ExcellentFun.instIsOfAddMonoidHomSurjective_of_TwoThreeTorsionFree
    [NonAssocRing R] [AddCancelCommMonoid G] [IsTorsionFreeBy G 2] [IsTorsionFreeBy G 3] :
    IsOfAddMonoidHomSurjective R G := by
  refine IsOfAddMonoidHomSurjective.mk' λ f x y ↦ ?_
  have h := nsmul_left_cancel (excellent_linear_formula f x (3 * y))
  rw [← mul_add, ← Nat.cast_ofNat, excellent_map_nat_mul,
    excellent_map_nat_mul, ← nsmul_add] at h
  exact nsmul_left_cancel h

instance NonperiodicGoodFun.instIsForallInjective_of_TwoTorsionFree
    [Ring R] [AddCancelMonoid G] [IsTorsionFreeBy G 2] (ι : G →+ R) :
    IsForallInjective ι where
  is_injective f a b h := by
    replace h : f (-(a - b)) = f (a - b) := by
      rw [neg_sub, map_sub_eq_iff_map_mul_eq ι h.symm h]
      exact map_mul_eq_of_map_eq_of_map_add_eq ι h.symm h (congrArg f (add_comm b a))
    replace h : f (a - b) = f 0 :=
      nsmul_left_cancel (n := 2) (by rw [← map_neg_add_map ι, h, two_nsmul])
    rwa [← map_zero_add_map_add_one ι, add_right_eq_self,
      map_eq_zero_iff_eq_one ι, add_left_eq_self, sub_eq_zero] at h
