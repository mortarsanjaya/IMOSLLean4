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

We prove more lemmas about good functions.
This file is separate from `IMOSLLean4/IMO2012/A6/A6Defs.lean` for using extra imports.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Additional lemmas on good functions -/

section

variable [Semiring R] [AddMonoid G] (ι : G →+ R) [FunLike F R G] [GoodFunClass F ι]
include ι

lemma map_mul_kernel_eq {f : F} (hd : f d = 0) (x) : f (x * d) = f 0 + f (x + d) := by
  rw [← good_def ι, hd, ι.map_zero, mul_zero]

lemma map_kernel_add_one_eq {f : F} (hd : f d = 0) : f 0 + f (d + 1) = 0 := by
  rw [add_comm, ← map_mul_kernel_eq ι hd, one_mul, hd]

end


section

variable [Semiring R] [AddCancelMonoid G] (ι : G →+ R) [FunLike F R G] [GoodFunClass F ι]
include ι

/-- Periodicity of zeroes of `f` -/
theorem period_of_map_eq_zero' {f : F} (hc : f c = 0) :
    ∀ x, f (x + c * c + c) = f (x + c * c + 1) := by
  have hc0 : ∀ x, f (x * c) = f 0 + f (x + c) := map_mul_kernel_eq ι hc
  ---- First prove `f(c^2) = f(c^3) = 0`
  obtain ⟨h0, h1⟩ : f (c * c) = 0 ∧ f (c * c * c) = 0 := by
    have hc1 : f 0 + f (c + 1) = 0 := map_kernel_add_one_eq ι hc
    suffices f 0 + f (c + c) = 0 by
      refine ⟨(hc0 c).trans this, ?_⟩
      replace hc1 : f (c + c) = f (c + 1) := add_left_cancel (this.trans hc1.symm)
      rw [hc0, ← add_one_mul, hc0, add_right_comm, map_add_one_eq_of_map_eq ι hc1,
        add_assoc, add_comm, ← hc0, add_one_mul, one_mul, this]
    obtain ⟨b, hb⟩ : ∃ b, f b = f 0 + f 0 := by
      refine ⟨ι (f 0) * ι (f (c + 1)), ?_⟩
      rw [← add_right_cancel_iff, map_incl_map_zero_mul_incl_map_add_map,
        add_assoc, hc1, add_zero]
    replace hc0 : _ + _ = _ + _ :=
      congrArg (· + f (c + 1)) (map_incl_map_zero_mul_incl_map_add_map ι f b)
    rw [hb, ι.map_add, ← mul_two, ← mul_assoc, ← add_assoc, add_assoc, hc1, add_zero] at hc0
    replace hc0 : f 0 + f (ι (f 0) * ι (f 0) * 2) = 0 := by
      rw [← add_right_cancel_iff, add_assoc, hc0, zero_add, add_zero]
    replace hb : f (ι (f 0) * ι (f 0)) = f c :=
      (map_incl_map_zero_mul_self ι f).trans hc.symm
    rwa [← Nat.cast_two, map_mul_nat_eq_of_map_eq ι hb, Nat.cast_two, mul_two] at hc0
  ---- Now write `f(xc^4)` in two ways
  intro x; rw [← add_left_cancel_iff, ← hc0, add_mul, add_right_comm,
    ← map_mul_kernel_eq ι h0, add_one_mul, ← add_left_cancel_iff,
    ← map_mul_kernel_eq ι h1, ← map_mul_kernel_eq ι h0]
  simp_rw [mul_assoc]

theorem map_add_incl_map_zero_mul_self (f : F) (x) :
    f (x + ι (f 0) * ι (f 0)) = f (x + 1) := by
  let C := ι (f 0) * ι (f 0)
  have h : f C = 0 := map_incl_map_zero_mul_self ι f
  obtain ⟨d, hd⟩ : ∃ d, d + C * C = 0 := by
    refine ⟨C * (ι (f 0) * ι (f (C + 1))), ?_⟩
    rw [← mul_add, add_comm, ← mul_add, ← ι.map_add,
      map_kernel_add_one_eq ι h, ι.map_zero, mul_zero, mul_zero]
  have h0 := period_of_map_eq_zero' ι h (x + d)
  rwa [add_assoc x, hd, add_zero] at h0

theorem map_one_eq_zero (f : F) : f 1 = 0 := by
  rw [← zero_add 1, ← map_add_incl_map_zero_mul_self ι, zero_add]
  exact map_incl_map_zero_mul_self ι f

theorem map_zero_add_map_add_one (f : F) (x) : f 0 + f (x + 1) = f x := by
  simpa only [mul_one] using (map_mul_kernel_eq ι (map_one_eq_zero ι f) x).symm

theorem map_zero_add_map_add_nat (f : F) (x) (n : ℕ) : n • f 0 + f (x + n) = f x := by
  induction n with
  | zero => simp [zero_nsmul]
  | succ n n_ih => rw [Nat.cast_succ, ← add_assoc, succ_nsmul,
      add_assoc, map_zero_add_map_add_one ι, n_ih]

end


/-- Custom cancellation lemma for non-commutative `G` case. -/
theorem map_eq_of_map_add_map_left_eq_map_add_map_right
    [NonUnitalNonAssocSemiring R] [IsCancelAdd R] [AddZeroClass G] [IsCancelAdd G]
    (ι : G →+ R) [FunLike F R G] [GoodFunClass F ι]
    {f : F} (h : f a + f b = f b + f c) : f a = f c := by
  replace h : ι (f a + f b) = ι (f b + f c) := congrArg ι h
  rw [ι.map_add, add_comm, ι.map_add, add_right_inj] at h
  exact map_eq_of_incl_map_eq ι h


section

variable [Ring R] [AddCancelMonoid G] (ι : G →+ R)
  [FunLike F R G] [GoodFunClass F ι] (f : F) (x : R)
include ι

theorem map_sub_one : f (x - 1) = f 0 + f x := by
  simpa only [sub_add_cancel] using (map_zero_add_map_add_one ι f (x - 1)).symm

theorem map_neg_incl_map_zero_mul_incl_map : f (-(ι (f 0) * ι (f x))) = f (x - 1) := by
  have h : ι (f (ι (f 0) * ι (f x))) = ι (f 0) - ι (f x) := by
    rw [eq_sub_iff_add_eq, ← ι.map_add, map_incl_map_zero_mul_incl_map_add_map]
  have h0 : f (ι (f 0) * ι (f (ι (f 0) * ι (f x)))) = f x := by
    apply map_eq_of_map_add_map_left_eq_map_add_map_right ι
    rw [map_incl_map_zero_mul_incl_map_add_map, map_incl_map_zero_mul_incl_map_add_map]
  rw [h, mul_sub, ← neg_add_eq_sub, map_add_incl_map_zero_mul_self] at h0
  rw [← map_zero_add_map_add_one ι f, h0, map_sub_one ι]

theorem map_incl_map_zero_mul_incl_map_eq_map_one_sub :
    f (ι (f 0) * ι (f x)) = f (1 - x) := by
  rw [← map_neg_eq_iff_map_eq ι, map_neg_incl_map_zero_mul_incl_map, neg_sub]

theorem map_one_sub_add_map : f (1 - x) + f x = f 0 := by
  rw [← map_incl_map_zero_mul_incl_map_eq_map_one_sub ι,
    map_incl_map_zero_mul_incl_map_add_map]

theorem map_add_map_one_sub : f x + f (1 - x) = f 0 := by
  simpa only [sub_sub_cancel] using map_one_sub_add_map ι f (1 - x)

theorem map_neg_add_map : f (-x) + f x = 2 • f 0 := by
  rw [← map_zero_add_map_add_one ι, neg_add_eq_sub,
    add_assoc, map_one_sub_add_map ι, two_nsmul]

end





/-! ### Additional lemmas on non-periodic good functions -/

section

variable [Semiring R] [IsCancelAdd R] [AddCancelMonoid G] (ι : G →+ R)
  [FunLike F R G] [NonperiodicGoodFunClass F ι]
include ι

theorem map_eq_zero_imp_eq_one {f : F} (h : f c = 0) : c = 1 := by
  refine add_left_cancel (a := c * c) (period_imp_eq ι (f := f) λ x ↦ ?_)
  rw [← add_assoc, ← add_assoc, period_of_map_eq_zero' ι h]

theorem map_eq_zero_iff_eq_one {f : F} : f x = 0 ↔ x = 1 :=
  ⟨map_eq_zero_imp_eq_one ι, λ h ↦ h ▸ map_one_eq_zero ι f⟩

theorem incl_map_zero_mul_self (f : F) : ι (f 0) * ι (f 0) = 1 :=
  map_eq_zero_imp_eq_one ι (map_incl_map_zero_mul_self ι f)

end


theorem incl_map_zero_comm_incl_map [Ring R] [AddCancelMonoid G]
    (ι : G →+ R) [FunLike F R G] [NonperiodicGoodFunClass F ι] (f : F) (x) :
    ι (f 0) * ι (f x) = ι (f x) * ι (f 0) := by
  have X (x) : f (ι (f (1 - x)) * ι (f x)) = f ((1 - x) * x) := by
    rw [← good_def ι f (1 - x), sub_add_cancel, map_one_eq_zero ι, add_zero]
  have h := good_def ι f (ι (f (1 - x)) * ι (f 0)) (ι (f 0) * ι (f x))
  rwa [map_incl_map_zero_mul_incl_map_eq_map_one_sub, map_incl_map_comm_incl_map_zero,
    map_incl_map_zero_mul_incl_map_eq_map_one_sub, X, sub_sub_cancel, mul_one_sub,
    mul_assoc, ← mul_assoc (ι (f 0)), incl_map_zero_mul_self, one_mul, X, one_sub_mul,
    add_right_eq_self, map_eq_zero_iff_eq_one ι, ← add_right_inj (a := ι (f x) * ι (f 0)),
    ← add_assoc, ← add_mul, ← ι.map_add, map_add_map_one_sub ι, incl_map_zero_mul_self,
    add_comm, add_left_inj] at h
