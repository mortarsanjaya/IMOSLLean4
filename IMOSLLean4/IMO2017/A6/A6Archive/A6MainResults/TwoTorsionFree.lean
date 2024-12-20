/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Basic
import IMOSLLean4.IMO2017.A6.ExcellentFun.OfAddHom.TorsionFree
import Mathlib.Algebra.Ring.Basic

/-!
# IMO 2017 A6 (P2, Solution to reduced version with `2 ∈ R⁰`)

We find all reduced good functions `f : R → R` when `2 ∈ R⁰`.
Here, `R⁰` is the set of non-zero-divisors of `R`.
-/

namespace IMOSL
namespace IMO2017A6

variable [Ring R] [AddCommGroup S] (hS2 : ∀ x y : S, 2 • x = 2 • y → x = y)
include hS2


section

variable (ι : S →+ R) [FunLike F R S] [NonperiodicGoodFunClass F ι] (f : F)
include ι

theorem TwoTorsionFree_eq_zero_of_map_neg_eq_of_map_eq
    {f : F} (h : f (-x) = f x) : x = 0 := by
  rw [map_neg_eq ι, sub_eq_iff_eq_add, ← two_nsmul] at h
  replace h := hS2 _ _ h
  rwa [eq_comm, ← sub_eq_zero, ← map_add_one ι, map_eq_zero_iff ι, add_left_eq_self] at h

theorem TwoTorsionFree_injective : (f : R → S).Injective := λ c d h ↦ by
  rw [← add_right_cancel_iff (a := -d), add_neg_cancel]
  apply TwoTorsionFree_eq_zero_of_map_neg_eq_of_map_eq hS2 ι (f := f)
  ---- Now focus on proving that `f(c - d) = f(d - c)`
  have h0 : f (-c) = f (-d) := map_neg_eq_of_map_eq ι h
  have h1 : f (c * d) = f (d * c) := by rw [← good_def ι, ← good_def ι f d, h, add_comm c]
  replace h1 : f (-(c * d)) = f (-(d * c)) := map_neg_eq_of_map_eq ι h1
  have h2 := good_def ι f c (-d)
  rw [mul_neg, h1, h, ← h0, ← mul_neg, ← good_def ι f d, add_right_inj] at h2
  rw [h2, neg_add_rev, neg_neg]

theorem TwoTorsionFree_solution :
    ∃ a : {a : R // a * a = 1 ∧ ∀ x, a * x = x * a}, ∀ x, ι (f x) = a * (1 - x) :=
  solution_of_injective ι (TwoTorsionFree_injective hS2 ι f)

end


def TwoTorsionFree_mkExcellentFun (ι : S →+ R) (f : NonperiodicGoodFun ι) :
    ExcellentFun R S where
  toFun x := f (1 - x)
  excellent_def' x y := by
    simp only [sub_sub_cancel]
    rw [add_sub_assoc, ← one_sub_mul, ← sub_sub, ← mul_one_sub, ← good_def ι f x y]
    obtain ⟨⟨a, ha, ha0⟩, h⟩ := TwoTorsionFree_solution hS2 ι f
    rw [h, h, ha0, mul_assoc, ← mul_assoc a, ha, one_mul]


variable (hS3 : ∀ x y : S, 3 • x = 3 • y → x = y) (ι : S →+ R)
include hS3 ι

theorem TwoThreeTorsionFree_exists_hom (f : NonperiodicGoodFun ι) :
    ∃ (a : {a : R // a * a = 1 ∧ ∀ x, a * x = x * a}) (φ : R →+ S),
      (∀ x, ι (φ x) = x) ∧ (∀ x, f x = φ (a * (1 - x))) := by
  obtain ⟨a, ha⟩ := TwoTorsionFree_solution hS2 ι f
  obtain ⟨φ, hφ⟩ : ∃ φ : R →+ S, ∀ x, φ x = f (1 - x) := by
    haveI : ExcellentFun.IsOfAddMonoidHomSurjective R S :=
      ExcellentFun.instIsOfAddMonoidHomSurjectiveOfTorsionFree hS2 hS3
    exact ⟨(TwoTorsionFree_mkExcellentFun hS2 ι f).toAddMonoidHom, λ _ ↦ rfl⟩
  refine ⟨a, φ.comp (AddMonoidHom.mulLeft a.1), ?_, ?_⟩
  · intro x; change ι (φ (a.1 * x)) = x
    rw [hφ, ha, sub_sub_cancel, ← mul_assoc, a.2.1, one_mul]
  · intro x; change f x = φ (a.1 * _)
    rw [← mul_assoc, a.2.1, one_mul, hφ, sub_sub_cancel]

@[deprecated]
theorem TwoThreeTorsionFree_nonperiodicGood_iff :
    nonperiodicGood ι f ↔ ∃ (a : {a : R // a * a = 1 ∧ ∀ x, a * x = x * a}) (φ : R →+ S),
      (∀ x, ι (φ x) = x) ∧ (f = λ x ↦ φ (a * (1 - x))) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨a, φ, h, h0⟩ := TwoThreeTorsionFree_exists_hom hS2 hS3 ι f
    exact ⟨a, φ, h, funext h0⟩
  · rintro ⟨a, φ, h, h0⟩
    refine ⟨⟨⟨f, λ x y ↦ ?_⟩, λ c d h1 ↦ ?_⟩, rfl⟩
    · rw [h0, h, h, a.2.2, mul_assoc, ← mul_assoc a.1,
        a.2.1, one_mul, ← φ.map_add, ← mul_add]
      refine congrArg (λ x ↦ φ (a.1 * x)) ?_
      rw [mul_one_sub, one_sub_mul, sub_sub, sub_sub_cancel,
        ← add_sub_assoc x, sub_add_sub_cancel']
    · replace h1 : ι (f (0 + c)) = ι (f (0 + d)) := congrArg ι (h1 0)
      rw [zero_add, zero_add, h0, h, h] at h1
      replace h1 : a.1 * _ = a.1 * _ := congrArg (a.1 * ·) h1
      rwa [← mul_assoc, ← mul_assoc, a.2.1, one_mul, one_mul, sub_right_inj] at h1
