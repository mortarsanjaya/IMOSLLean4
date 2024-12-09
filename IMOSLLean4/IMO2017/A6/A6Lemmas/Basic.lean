/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Basic

/-!
# IMO 2017 A6 (P2, Basic properties)

We prove basic properties of good functions.
This file is separated from `IMOSLLean4/IMO2012/A6/A6Defs.lean`
  since it uses an extra import: `Mathlib/Algebra/Group/Basic.lean`.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Some good functions -/

section

variable (R) [NonAssocRing R]

def GoodFun.one_sub : GoodFun (id : R → R) where
  toFun x := 1 - x
  good_def' x y := by
    simp only [id]
    rw [mul_one_sub, one_sub_mul, sub_sub, sub_sub_cancel,
      ← add_sub_assoc x, sub_add_sub_cancel']

def NonperiodicGoodFun.one_sub : NonperiodicGoodFun (id : R → R) :=
  { GoodFun.one_sub R with
    period_imp_eq' := λ _ _ h ↦ add_right_injective 0 (sub_right_injective (h 0)) }

@[deprecated]
def GoodFun.sub_one : GoodFun (id : R → R) where
  toFun x := x - 1
  good_def' x y := by
    simp only [id]
    rw [sub_one_mul, mul_sub_one, sub_sub,
      sub_add_cancel, sub_sub, sub_add_sub_cancel]

@[deprecated]
def NonperiodicGoodFun.sub_one : NonperiodicGoodFun (id : R → R) :=
  { GoodFun.sub_one R with
    period_imp_eq' := λ _ _ h ↦ add_right_injective 0 (sub_left_injective (h 0)) }

end


section

variable [Semiring R] (a : {a : R // a * a = 1 ∧ ∀ x, a * x = x * a})

def GoodFun.mul_central_involutive (f : GoodFun (id : R → R)) : GoodFun (id : R → R) where
  toFun x := a * f x
  good_def' x y := by
    simp only [id]
    rw [a.2.2 (f x), mul_assoc, ← mul_assoc a.1 a.1, a.2.1,
      one_mul, ← mul_add, ← good_def id f x y]; rfl

def NonperiodicGoodFun.mul_central_involutive (f : NonperiodicGoodFun (id : R → R)) :
    NonperiodicGoodFun (id : R → R) :=
  { f.toGoodFun.mul_central_involutive a with
    period_imp_eq' := λ c d h ↦ f.period_imp_eq' c d λ x ↦ by
      replace h : a.1 * (a.1 * _) = a.1 * (a.1 * _) := congrArg (a.1 * ·) (h x)
      rwa [← mul_assoc, ← mul_assoc, a.2.1, one_mul, one_mul] at h }

end


section

variable [Ring R] (a : {a : R // a * a = 1 ∧ ∀ x, a * x = x * a})

@[deprecated]
theorem mul_one_sub_is_good : good id (λ x : R ↦ a * (1 - x)) :=
  ⟨(GoodFun.one_sub R).mul_central_involutive a, rfl⟩

@[deprecated]
theorem mul_one_sub_is_nonperiodicGood : nonperiodicGood id (λ x : R ↦ a * (1 - x)) :=
  ⟨(NonperiodicGoodFun.one_sub R).mul_central_involutive a, rfl⟩

end





/-! ### Properties of good function -/

lemma map_map_zero_mul_self
    [NonUnitalNonAssocSemiring R] [AddZeroClass S] [IsCancelAdd S] (ι : S → R)
    [FunLike F R S] [GoodFunClass F ι] (f : F) :
    f (ι (f 0) * ι (f 0)) = 0 := by
  rw [← add_right_cancel_iff, good_def, zero_add, mul_zero, add_zero]


section

variable [NonAssocSemiring R] [Add S] [IsCancelAdd S] (ι : S → R)
  [FunLike F R S] [GoodFunClass F ι] {f : F} (h : f a = f b)
include ι h

lemma map_add_one_eq_of_map_eq : f (a + 1) = f (b + 1) := by
  rw [← add_right_inj, good_def ι, mul_one, h, good_def ι, mul_one]

lemma map_add_nat_eq_of_map_eq : ∀ n : ℕ, f (a + n) = f (b + n) :=
  Nat.rec (by rw [Nat.cast_zero, add_zero, add_zero, h]) λ n hn ↦ by
    rw [Nat.cast_succ, ← add_assoc, ← add_assoc]
    exact map_add_one_eq_of_map_eq ι hn

lemma map_mul_nat_eq_of_map_eq (n : ℕ) : f (a * n) = f (b * n) := by
  rw [← good_def ι, map_add_nat_eq_of_map_eq ι h, h, good_def]

end


lemma map_neg_eq_of_map_eq
    [NonAssocRing R] [Add S] [IsCancelAdd S] (ι : S → R)
    [FunLike F R S] [GoodFunClass F ι] {f : F} (h : f a = f b) :
    f (-a) = f (-b) := by
  have h0 : f ((a + 1) * -1) = f ((b + 1) * -1) := by
    rw [← good_def ι, map_add_one_eq_of_map_eq ι h, add_neg_cancel_right,
      h, ← good_def ι f (b + 1), add_neg_cancel_right]
  replace h0 := map_add_one_eq_of_map_eq ι h0
  rwa [mul_neg_one, mul_neg_one, neg_add_rev,
    neg_add_cancel_comm, neg_add_rev, neg_add_cancel_comm] at h0


section

variable [Semiring R] [AddCancelMonoid S] (ι : S →+ R)
  [FunLike F R S] [GoodFunClass F ι] (f : F)
include ι

lemma map_mul_kernel_eq {f : F} (hd : f d = 0) (x) : f (x * d) = f 0 + f (x + d) := by
  rw [← good_def ι, hd, ι.map_zero, mul_zero]

lemma map_kernel_add_one_eq {f : F} (hd : f d = 0) : f 0 + f (d + 1) = 0 := by
  rw [add_comm, ← map_mul_kernel_eq ι hd, one_mul, hd]

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
      rw [← add_right_cancel_iff, map_map_zero_mul_map, add_assoc, hc1, add_zero]
    replace hc0 : _ + _ = _ + _ := congrArg (· + f (c + 1)) (map_map_zero_mul_map ι f b)
    rw [hb, ι.map_add, ← mul_two, ← mul_assoc, ← add_assoc, add_assoc, hc1, add_zero] at hc0
    replace hc0 : f 0 + f (ι (f 0) * ι (f 0) * 2) = 0 := by
      rw [← add_right_cancel_iff, add_assoc, hc0, zero_add, add_zero]
    replace hb : f (ι (f 0) * ι (f 0)) = f c := (map_map_zero_mul_self ι f).trans hc.symm
    rwa [← Nat.cast_two, map_mul_nat_eq_of_map_eq ι hb, Nat.cast_two, mul_two] at hc0
  ---- Now write `f(xc^4)` in two ways
  intro x; rw [← add_left_cancel_iff, ← hc0, add_mul, add_right_comm,
    ← map_mul_kernel_eq ι h0, add_one_mul, ← add_left_cancel_iff,
    ← map_mul_kernel_eq ι h1, ← map_mul_kernel_eq ι h0]
  repeat rw [mul_assoc]

theorem incl_map_zero_mul_self_period_one (x) : f (x + ι (f 0) * ι (f 0)) = f (x + 1) := by
  let C := ι (f 0) * ι (f 0)
  have h : f C = 0 := map_map_zero_mul_self ι f
  obtain ⟨d, hd⟩ : ∃ d, d + C * C = 0 := by
    refine ⟨C * (ι (f 0) * ι (f (C + 1))), ?_⟩
    rw [← mul_add, add_comm, ← mul_add, ← ι.map_add,
      map_kernel_add_one_eq ι h, ι.map_zero, mul_zero, mul_zero]
  have h0 := period_of_map_eq_zero' ι h (x + d)
  rwa [add_assoc x, hd, add_zero] at h0

theorem map_one_eq_zero : f 1 = 0 := by
  have h := incl_map_zero_mul_self_period_one ι f 0
  rwa [zero_add, zero_add, map_map_zero_mul_self, eq_comm] at h

theorem map_add_one' (x) : f 0 + f (x + 1) = f x := by
  have h := good_def ι f x 1
  rwa [map_one_eq_zero ι, ι.map_zero, mul_zero, mul_one] at h

end


theorem map_add_one [Semiring R] [AddCommGroup S] (ι : S →+ R)
    [FunLike F R S] [GoodFunClass F ι] (f : F) (x) : f (x + 1) = f x - f 0 :=
  eq_sub_of_add_eq' (map_add_one' ι f x)

theorem map_sub_one [Ring R] [AddCancelCommMonoid S] (ι : S →+ R)
    [FunLike F R S] [GoodFunClass F ι] (f : F) (x) : f (x - 1) = f x + f 0 := by
  rw [← map_add_one' ι, sub_add_cancel, add_comm]


section

variable [Ring R] [AddCommGroup S] (ι : S →+ R) [FunLike F R S] [GoodFunClass F ι] (f : F)
include ι

theorem map_one_sub' (x) : f (1 - x) = f (ι (f 0) * ι (f x)) := by
  have h := map_map_zero_mul_map ι f (ι (f 0) * ι (f x))
  rw [eq_sub_of_add_eq (map_map_zero_mul_map ι f x), ← eq_sub_iff_add_eq, sub_sub_cancel,
    ι.map_sub, mul_sub, sub_eq_neg_add, incl_map_zero_mul_self_period_one, map_add_one ι,
    sub_eq_iff_eq_add, ← map_sub_one ι] at h
  replace h := map_neg_eq_of_map_eq ι h
  rwa [eq_comm, neg_neg, neg_sub] at h

theorem map_one_sub (x) : f (1 - x) = f 0 - f x := by
  rw [map_one_sub' ι, eq_sub_iff_add_eq, map_map_zero_mul_map]

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
  rw [h, ι.map_neg, mul_neg, map_neg_eq ι, ← add_assoc, map_add_one ι, map_add_one ι,
    eq_sub_of_add_eq (map_map_mul_map_zero ι f x), sub_sub, ← add_sub_right_comm,
    two_nsmul, add_sub_cancel, ← sub_add, ← add_sub_right_comm, ← two_nsmul] at h0
  rw [h0, one_add_one_eq_two]

end





/-! ##### If `f` is injective, we are done -/

section

variable [Ring R] [AddCommGroup S] (ι : S →+ R)
  [FunLike F R S] [GoodFunClass F ι] {f : F} (h : (f : R → S).Injective)
include h

theorem incl_map_zero_mul_self_of_injective : ι (f 0) * ι (f 0) = 1 :=
  h ((map_map_zero_mul_self ι f).trans (map_one_eq_zero ι f).symm)

theorem solution_of_injective (x) : ι (f x) = ι (f 0) * (1 - x) := by
  have X := map_map_zero_mul_map ι f
  have h0 := X (ι (f 0) * ι (f x))
  rw [eq_sub_of_add_eq (X x), ι.map_sub, mul_sub, add_sub_left_comm, add_right_eq_self] at h0
  replace X := incl_map_zero_mul_self_of_injective ι h
  replace h0 := h (eq_of_sub_eq_zero h0)
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', X] at h0
  rw [h0, ← mul_assoc, X, one_mul]

theorem incl_map_zero_comm_of_injective (x) : ι (f 0) * x = x * ι (f 0) := by
  have h0 : ι (f 0) * ι (f (1 - x)) = ι (f (1 - x)) * ι (f 0) := by
    apply h; rw [← add_left_inj, good_def, zero_mul, add_comm 0, good_def, mul_zero]
  rw [solution_of_injective ι h (1 - x), sub_sub_cancel, mul_assoc] at h0
  replace h0 : (ι (f 0) * ι (f 0)) * (ι (f 0) * x) = (ι (f 0) * ι (f 0)) * (x * ι (f 0)) := by
    rw [mul_assoc, h0, mul_assoc]
  rwa [incl_map_zero_mul_self_of_injective ι h, one_mul, one_mul] at h0

end





/-! ### Properties of non-periodic good function -/

variable [Ring R] [AddCommGroup S] (ι : S →+ R)
  [FunLike F R S] [NonperiodicGoodFunClass F ι]
include ι

theorem map_eq_zero_iff {f : F} : f c = 0 ↔ c = 1 := by
  refine ⟨λ h ↦ period_imp_eq ι (f := f) λ x ↦ ?_, λ h ↦ h ▸ map_one_eq_zero ι f⟩
  have h := period_of_map_eq_zero' ι h (x - c * c)
  rwa [sub_add_cancel] at h

theorem incl_map_zero_mul_self (f : F) : ι (f 0) * ι (f 0) = 1 :=
  (map_eq_zero_iff ι).mp (map_map_zero_mul_self ι f)
