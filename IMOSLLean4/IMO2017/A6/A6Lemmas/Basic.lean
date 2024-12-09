/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Defs
import Mathlib.Algebra.Group.Basic

/-!
# IMO 2017 A6 (P2, Basic properties)

We prove basic properties of good functions.
This file is separated from `IMOSLLean4/IMO2012/A6/A6Defs.lean`
  since it uses an extra import: `Mathlib/Algebra/Group/Basic.lean`.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Construction of some good functions -/

section

variable (R) [NonAssocRing R]

def GoodFun_one_sub : GoodFun R where
  toFun := λ x ↦ 1 - x
  good_def' := λ x y ↦ by simp only; rw [mul_one_sub, one_sub_mul,
    sub_sub, sub_sub_cancel, ← add_sub_assoc x, sub_add_sub_cancel']

def NonperiodicGoodFun_one_sub : NonperiodicGoodFun R :=
  { GoodFun_one_sub R with
    period_imp_eq' := λ _ _ h ↦ add_right_injective 0 (sub_right_injective (h 0)) }

@[deprecated]
def GoodFun_sub_one : GoodFun R where
  toFun := λ x ↦ x - 1
  good_def' := λ x y ↦ by simp only; rw [sub_one_mul, mul_sub_one,
    sub_sub, sub_add_cancel, sub_sub, sub_add_sub_cancel]

@[deprecated]
def NonperiodicGoodFun_sub_one : NonperiodicGoodFun R :=
  { GoodFun_sub_one R with
    period_imp_eq' := λ _ _ h ↦ add_right_injective 0 (sub_left_injective (h 0)) }

end


section

variable [Semiring R] (a : {a : R // a * a = 1 ∧ ∀ x, a * x = x * a})

def GoodFun.mul_central_involutive (f : GoodFun R) : GoodFun R where
  toFun := λ x ↦ a * f x
  good_def' := λ x y ↦ by rw [mul_assoc, ← mul_assoc _ a.val, ← a.property.2,
    mul_assoc, ← mul_assoc, a.property.1, one_mul, ← mul_add, good_def]

def NonperiodicGoodFun.mul_central_involutive (f : NonperiodicGoodFun R) :
    NonperiodicGoodFun R :=
  { f.toGoodFun.mul_central_involutive a with
    period_imp_eq' := λ c d h ↦ f.period_imp_eq' c d λ x ↦ by
      replace h : a * (a * f (x + c)) = a * (a * f (x + d)) := congrArg (a.val * ·) (h x)
      rwa [← mul_assoc, ← mul_assoc, a.property.1, one_mul, one_mul] at h }

end





/-! ### Properties of good function -/

lemma map_add_one_eq_of_map_eq [NonAssocSemiring R] [IsCancelAdd R]
    [FunLike F R R] [GoodFunClass F R] {f : F} (h : f a = f b) :
    f (a + 1) = f (b + 1) := by
  rw [← add_right_inj, good_def, mul_one, h, good_def, mul_one]

@[deprecated]
lemma map_neg_eq_of_map_eq [NonAssocRing R] [FunLike F R R] [GoodFunClass F R]
    {f : F} (h : f a = f b) : f (-a) = f (-b) := by
  have h0 : f ((a + 1) * -1) = f ((b + 1) * -1) := by
    rw [← good_def, map_add_one_eq_of_map_eq h, add_neg_cancel_right,
      h, ← good_def f (b + 1), add_neg_cancel_right]
  replace h0 := map_add_one_eq_of_map_eq h0
  rwa [mul_neg_one (α := R), mul_neg_one (α := R), neg_add_rev,
    neg_add_cancel_comm, neg_add_rev, neg_add_cancel_comm] at h0


section

variable [Ring R] [FunLike F R R] [GoodFunClass F R]

/-- Periodicity of zeroes of `f`. -/
theorem period_of_map_eq_zero {f : F} (h : f C = 0) : ∀ x, f (x + C) = f (x + 1) := by
  have hC (x) : f (C * x) = f 0 + f (C + x) := by rw [← good_def, h, zero_mul]
  have h0 : f (C + 1) = -f 0 := by
    have h0 := hC 1; rwa [mul_one, h, eq_comm, add_eq_zero_iff_neg_eq, eq_comm] at h0
  have h1 : f (f 0 * f 0 * 2) = -f 0 := by
    have h1 : f (C * -C) = f 0 * 2 := by rw [hC, add_neg_cancel, mul_two]
    have h2 := map_map_zero_mul_map f (C * -C)
    rwa [h1, ← mul_assoc, ← eq_sub_iff_add_eq, mul_two (f 0), sub_add_cancel_right] at h2
  replace h1 : f (C * 2) = -f 0 := by
    have X := map_map_zero_mul_self f
    have h2 := map_add_one_eq_of_map_eq (map_add_one_eq_of_map_eq (h.trans X.symm))
    rw [add_assoc, add_assoc, one_add_one_eq_two] at h2
    rw [hC, h2, ← h1, ← good_def, X, zero_mul]
  have h2 : f (C * C) = 0 := by rw [hC, ← mul_two, h1, add_neg_cancel]
  have h3 : f (C * (C * C)) = 0 := by
    rw [hC, ← mul_one_add C, hC, add_left_comm C, ← mul_two,
      add_comm 1, map_add_one_eq_of_map_eq (h1.trans h0.symm),
      add_assoc, one_add_one_eq_two, ← hC, h1, add_neg_cancel]
  ---- Now finish by decomposing `f(C^4 x)` in two ways
  intro y; let x := y - C * C
  have h4 := good_def f (C * C) (C * C * x)
  rw [h2, zero_mul, ← mul_one_add _ x, ← good_def, h2, zero_mul, mul_assoc C C x,
    ← mul_assoc, mul_assoc C, ← good_def, h3, zero_mul, add_right_inj, ← mul_add,
    add_left_comm _ 1, add_sub_cancel, hC, add_right_inj, add_comm, add_comm C] at h4
  exact h4.symm


section

variable (f : F)

theorem map_one_eq_zero : f 1 = 0 := by
  have X := map_map_zero_mul_self f
  rw [← zero_add 1, ← period_of_map_eq_zero X, zero_add, X]

theorem map_add_one' (x) : f 0 + f (x + 1) = f x := by
  have h := good_def f x 1; rwa [map_one_eq_zero, mul_zero, mul_one] at h

theorem map_add_one (x) : f (x + 1) = f x - f 0 :=
  eq_sub_of_add_eq' (map_add_one' f x)

theorem map_sub_one (x) : f (x - 1) = f x + f 0 := by
  rw [← map_add_one', sub_add_cancel, add_comm]

end





/-! ##### If `f` is injective, we are done -/

section

variable {f : F} (h : (f : R → R).Injective)
include h

theorem map_zero_mul_self_of_injective : f 0 * f 0 = 1 :=
  h ((map_map_zero_mul_self f).trans (map_one_eq_zero f).symm)

theorem solution_of_injective (x) : f x = f 0 * (1 - x) := by
  have X := map_map_zero_mul_map f
  have h0 := X (f 0 * f x)
  rw [eq_sub_of_add_eq (X x), mul_sub, add_sub_left_comm, add_right_eq_self] at h0
  replace X := map_zero_mul_self_of_injective h
  replace h0 := h (eq_of_sub_eq_zero h0)
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', X] at h0
  rw [h0, ← mul_assoc, X, one_mul]

theorem map_zero_comm_of_injective (x) : f 0 * x = x * f 0 := by
  have h0 : f 0 * f (1 - x) = f (1 - x) * f 0 := by
    apply h; rw [← add_left_inj, good_def, zero_mul, add_comm 0, good_def, mul_zero]
  rw [solution_of_injective h (1 - x), sub_sub_cancel, mul_assoc] at h0
  replace h0 : (f 0 * f 0) * (f 0 * x) = (f 0 * f 0) * (x * f 0) := by
    rw [mul_assoc, h0, mul_assoc]
  rwa [map_zero_mul_self_of_injective h, one_mul, one_mul] at h0

end

end





/-! ### Properties of non-periodic good function -/

variable [Ring R] [FunLike F R R] [NonperiodicGoodFunClass F R]

theorem map_eq_zero_iff {f : F} : f c = 0 ↔ c = 1 :=
  ⟨λ h ↦ period_imp_eq (period_of_map_eq_zero h), λ h ↦ h ▸ map_one_eq_zero f⟩

theorem map_zero_mul_self (f : F) : f 0 * f 0 = 1 :=
  map_eq_zero_iff.mp (map_map_zero_mul_self f)
