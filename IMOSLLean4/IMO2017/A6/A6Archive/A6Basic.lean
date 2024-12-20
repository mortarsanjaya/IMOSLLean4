/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Basic

/-!
# IMO 2017 A6 (P2, Additional lemmas on good functions)

We prove some more lemmas about good functions.
This file is separate from `IMOSLLean4/IMO2012/A6/A6Defs.lean` for using extra imports.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Properties of good function -/

lemma good_alt [Add R] [Mul R] [AddGroup G]
    (ι : G → R) [FunLike F R G] [GoodFunClass F ι] (f : F) (x y : R) :
    f (ι (f x) * ι (f y)) = f (x * y) - f (x + y) :=
  eq_sub_of_add_eq (good_def ι f x y)


section

variable [NonUnitalNonAssocSemiring R] [AddGroup G]
  (ι : G → R) [FunLike F R G] [GoodFunClass F ι] (f : F)

theorem map_map_zero_mul_map (x) : f (ι (f 0) * ι (f x)) = f 0 - f x :=
  eq_sub_of_add_eq (map_incl_map_zero_mul_incl_map_add_map ι f x)

theorem map_map_mul_map_zero (x) : f (ι (f x) * ι (f 0)) = f 0 - f x :=
  eq_sub_of_add_eq (map_incl_map_mul_incl_map_zero_add_map ι f x)

end


theorem map_add_one [Semiring R] [AddCommGroup G] (ι : G →+ R)
    [FunLike F R G] [StronglyGoodFunClass F ι] (f : F) (x) : f (x + 1) = f x - f 0 :=
  eq_sub_of_add_eq' (map_zero_add_map_add_one ι f x)


section

variable [Ring R] [AddCommGroup G] (ι : G →+ R) [FunLike F R G] [GoodFunClass F ι] (f : F)
include ι

theorem map_one_sub' (x) : f (1 - x) = f (ι (f 0) * ι (f x)) := by
  have h := map_map_zero_mul_map_add_map ι f (ι (f 0) * ι (f x))
  rw [map_map_zero_mul_map ι f x, ← eq_sub_iff_add_eq, sub_sub_cancel,
    ι.map_sub, mul_sub, sub_eq_neg_add, incl_map_zero_mul_self_period_one,
    map_add_one ι, sub_eq_iff_eq_add, ← map_sub_one ι] at h
  replace h := map_neg_eq_of_map_eq ι h
  rwa [eq_comm, neg_neg, neg_sub] at h

theorem map_one_sub (x) : f (1 - x) = f 0 - f x := by
  rw [map_one_sub' ι, map_map_zero_mul_map]

theorem map_one_sub'' (x) : f (1 - x) = f (ι (f x) * ι (f 0)) := by
  rw [map_one_sub ι, map_map_mul_map_zero]

theorem map_neg_add_map_eq (x) : f (-x) + f x = 2 • f 0 := by
  have h := add_eq_of_eq_sub (map_one_sub ι f x)
  rwa [sub_eq_neg_add, map_add_one ι, ← add_sub_right_comm,
    sub_eq_iff_eq_add, ← two_nsmul] at h

theorem map_neg_eq (x) : f (-x) = 2 • f 0 - f x :=
  eq_sub_of_add_eq (map_neg_add_map_eq ι f x)

theorem map_mul_two_eq (x) : f (x * 2) = 2 • f x - f 0 := by
  have h : f (1 + 1) = -f 0 := by
    rw [map_add_one ι, map_one_eq_zero ι, zero_sub]
  have h0 := good_def ι f x (1 + 1)
  rw [h, ι.map_neg, mul_neg, map_neg_eq ι, ← add_assoc, map_add_one ι,
    map_add_one ι, map_map_mul_map_zero, sub_sub, ← add_sub_right_comm,
    two_nsmul, add_sub_cancel, ← sub_add, ← add_sub_right_comm, ← two_nsmul] at h0
  rw [h0, one_add_one_eq_two]

end





/-! ### Properties of non-periodic good function -/

section

variable [Ring R] [AddCommGroup G] (ι : G →+ R)
  [FunLike F R G] [NonperiodicGoodFunClass F ι]
include ι

theorem incl_map_zero_comm_incl_map (f : F) (x : R) :
    ι (f 0) * ι (f x) = ι (f x) * ι (f 0) := by
  have h := good_def ι f (ι (f x) * ι (f 0)) (ι (f 0) * ι (f (1 - x)))
  rw [← map_one_sub'', ← map_one_sub', sub_sub_cancel, good_alt, one_sub_mul, mul_assoc,
    ← mul_assoc (ι (f 0)), incl_map_zero_mul_self, one_mul, good_alt, mul_one_sub,
    sub_add_cancel, add_sub_cancel, add_right_eq_self, map_eq_zero_iff ι, map_one_sub ι,
    ι.map_sub, mul_sub, incl_map_zero_mul_self, add_sub_left_comm, add_right_eq_self] at h
  exact (eq_of_sub_eq_zero h).symm

end





/-! ### If `f` is injective, we are done -/

/-- This should be moved somewhere. -/
theorem solution_of_injective [Ring R] [AddCommGroup G] (ι : G →+ R)
    [FunLike F R G] [GoodFunClass F ι] {f : F} (h : (f : R → G).Injective) :
    ∃ a : {a : R // a * a = 1 ∧ ∀ x, a * x = x * a}, ∀ x, ι (f x) = a * (1 - x) := by
  have h0 : ι (f 0) * ι (f 0) = 1 :=
    h ((map_map_zero_mul_self ι f).trans (map_one_eq_zero ι f).symm)
  have h1 (x) : ι (f x) = ι (f 0) * (1 - x) := by
    have X := map_map_zero_mul_map_add_map ι f
    have h1 := X (ι (f 0) * ι (f x))
    rw [eq_sub_of_add_eq (X x), ι.map_sub, mul_sub,
      add_sub_left_comm, add_right_eq_self] at h1
    replace h1 := h (eq_of_sub_eq_zero h1)
    rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', h0] at h1
    rw [h1, ← mul_assoc, h0, one_mul]
  have h2 (x) : ι (f 0) * x = x * ι (f 0) := by
    have h2 : ι (f 0) * ι (f (1 - x)) = ι (f (1 - x)) * ι (f 0) := by
      apply h; rw [← add_left_inj, good_def, zero_mul, add_comm 0, good_def, mul_zero]
    rw [h1 (1 - x), sub_sub_cancel, mul_assoc] at h2
    replace h2 : (ι (f 0) * ι (f 0)) * (ι (f 0) * x)
        = (ι (f 0) * ι (f 0)) * (x * ι (f 0)) := by
      rw [mul_assoc, h2, mul_assoc]
    rwa [h0, one_mul, one_mul] at h2
  exact ⟨⟨ι (f 0), h0, h2⟩, h1⟩
