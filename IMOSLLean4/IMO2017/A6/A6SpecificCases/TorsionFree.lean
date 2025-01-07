/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Basic

/-!
# IMO 2017 A6 (P2, Classifying good functions: 2- and 3-torsion-free case)

We solve the problem when `G` is `2`-torsion free and `3`-torsion free.

TODO: Move this to the main file `A6.lean`.
-/

namespace IMOSL
namespace IMO2017A6

theorem NonperiodicGoodFun.injective_of_TwoTorsionFree
    [Ring R] [AddCancelMonoid G] (hG2 : ∀ x y : G, 2 • x = 2 • y → x = y)
    {ι : G →+ R} (f : NonperiodicGoodFun ι) : Function.Injective f := by
  intro a b h
  replace h : f (-(a - b)) = f (a - b) := by
    rw [neg_sub, map_sub_eq_iff_map_mul_eq ι h.symm h]
    exact map_mul_eq_of_map_eq_of_map_add_eq ι h.symm h (congrArg f (add_comm b a))
  replace h : f (a - b) = f 0 :=
    hG2 _ _ (by rw [← map_neg_add_map ι, h, two_nsmul])
  rwa [← map_zero_add_map_add_one ι, add_right_eq_self,
    map_eq_zero_iff_eq_one ι, add_left_eq_self, sub_eq_zero] at h
