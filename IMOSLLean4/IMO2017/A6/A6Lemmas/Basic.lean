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

/-! ### Some good functions -/

theorem zero_is_good [NonUnitalNonAssocSemiring R] : good (λ _ : R ↦ 0) :=
  λ _ _ ↦ zero_add 0


section

variable [NonAssocRing R]

theorem one_sub_is_good : good (λ x : R ↦ 1 - x) := λ x y ↦ by
  simp only; rw [mul_one_sub, one_sub_mul, sub_sub,
    sub_sub_cancel, ← add_sub_assoc x, sub_add_sub_cancel']

theorem one_sub_is_ReducedGood : ReducedGood (λ x : R ↦ 1 - x) :=
  ⟨one_sub_is_good, λ _ _ h ↦ add_right_injective 0 (sub_right_injective (h 0))⟩

theorem sub_one_is_good : good (λ x : R ↦ x - 1) := λ x y ↦ by
  simp only; rw [sub_one_mul, mul_sub_one, sub_sub,
    sub_add_cancel, sub_sub, sub_add_sub_cancel]

theorem sub_one_is_ReducedGood : ReducedGood (λ x : R ↦ x - 1) :=
  ⟨sub_one_is_good, λ _ _ h ↦ add_right_injective 0 (sub_left_injective (h 0))⟩

end


section

variable [Ring R] {a : R} (ha : a * a = 1) (ha0 : ∀ x, a * x = x * a)
include ha ha0

theorem good_mul_central_involutive {f : R → R} (hf : good f) :
    good (λ x : R ↦ a * f x) := λ x y ↦ by
  rw [mul_assoc, ← mul_assoc _ a, ← ha0, mul_assoc, ← mul_assoc, ha, one_mul, ← mul_add, hf]

theorem ReducedGood_mul_central_involutive {f : R → R} (hf : ReducedGood f) :
    ReducedGood (λ x : R ↦ a * f x) :=
  ⟨good_mul_central_involutive ha ha0 hf.is_good,
  λ c d h ↦ hf.period_imp_eq c d λ x ↦ by
    replace h : a * _ = a * _ := congrArg (a * ·) (h x)
    rwa [← mul_assoc, ← mul_assoc, ha, one_mul, one_mul] at h⟩

theorem mul_one_sub_is_good : good (λ x : R ↦ a * (1 - x)) :=
  good_mul_central_involutive ha ha0 one_sub_is_good

theorem mul_one_sub_is_ReducedGod : ReducedGood (λ x : R ↦ a * (1 - x)) :=
  ReducedGood_mul_central_involutive ha ha0 one_sub_is_ReducedGood

end





/-! ### Properties of good function -/

namespace good

lemma map_add_one_eq_of_map_eq [NonAssocSemiring R] [IsCancelAdd R]
    {f : R → R} (hf : good f) (h : f a = f b) : f (a + 1) = f (b + 1) := by
  rw [← add_right_inj, hf, mul_one, h, hf, mul_one]

lemma map_map_zero_mul_self [NonUnitalNonAssocRing R] {f : R → R} (hf : good f) :
    f (f 0 * f 0) = 0 := by
  rw [eq_sub_of_add_eq (hf 0 0), add_zero, mul_zero, sub_self]

lemma map_neg_eq_of_map_eq [NonAssocRing R] {f : R → R} (hf : good f) (h : f a = f b) :
    f (-a) = f (-b) := by
  have h0 : f ((a + 1) * -1) = f ((b + 1) * -1) := by
    rw [← hf, hf.map_add_one_eq_of_map_eq h, add_neg_cancel_right,
      h, ← hf (b + 1), add_neg_cancel_right]
  replace h0 := hf.map_add_one_eq_of_map_eq h0
  rwa [mul_neg_one (α := R), mul_neg_one (α := R), neg_add_rev,
    neg_add_cancel_comm, neg_add_rev, neg_add_cancel_comm] at h0


variable [Ring R] {f : R → R} (hf : good f)
include hf

/-- Periodicity of zeroes of `f` -/
theorem period_of_map_eq_zero (h : f C = 0) : ∀ x, f (x + C) = f (x + 1) := by
  have hC (x) : f (C * x) = f 0 + f (C + x) := by rw [← hf, h, zero_mul]
  have h0 : f (C + 1) = -f 0 := by
    have h0 := hC 1; rwa [mul_one, h, eq_comm, add_eq_zero_iff_neg_eq, eq_comm] at h0
  have h1 : f (f 0 * f 0 * 2) = -f 0 := by
    have h1 : f (C * -C) = f 0 * 2 := by rw [hC, add_neg_cancel, mul_two]
    have h2 := hf.map_map_zero_mul_map (C * -C)
    rwa [h1, ← mul_assoc, ← eq_sub_iff_add_eq, mul_two (f 0), sub_add_cancel_right] at h2
  replace h1 : f (C * 2) = -f 0 := by
    have X := hf.map_map_zero_mul_self
    have h2 := hf.map_add_one_eq_of_map_eq (hf.map_add_one_eq_of_map_eq (h.trans X.symm))
    rw [add_assoc, add_assoc, one_add_one_eq_two] at h2
    rw [hC, h2, ← h1, ← hf, X, zero_mul]
  have h2 : f (C * C) = 0 := by rw [hC, ← mul_two, h1, add_neg_cancel]
  have h3 : f (C * (C * C)) = 0 := by
    rw [hC, ← mul_one_add C, hC, add_left_comm C, ← mul_two,
      add_comm 1, hf.map_add_one_eq_of_map_eq (h1.trans h0.symm),
      add_assoc, one_add_one_eq_two, ← hC, h1, add_neg_cancel]
  ---- Now finish by decomposing `f(C^4 x)` in two ways
  intro y; let x := y - C * C
  have h4 := hf (C * C) (C * C * x)
  rwa [h2, zero_mul, ← mul_one_add _ x, ← hf, h2, zero_mul, mul_assoc C C x, ← mul_assoc,
    mul_assoc C, ← hf, h3, zero_mul, add_right_inj, ← mul_add, add_left_comm _ 1,
    add_sub_cancel, hC, add_right_inj, add_comm, add_comm C, eq_comm] at h4

theorem map_one_eq_zero : f 1 = 0 := by
  have X := hf.map_map_zero_mul_self
  rw [← zero_add 1, ← hf.period_of_map_eq_zero X, zero_add, X]

theorem map_add_one' (x) : f 0 + f (x + 1) = f x := by
  have h := hf x 1; rwa [hf.map_one_eq_zero, mul_zero, mul_one] at h

theorem map_add_one (x) : f (x + 1) = f x - f 0 :=
  eq_sub_of_add_eq' (hf.map_add_one' x)

theorem map_sub_one (x) : f (x - 1) = f x + f 0 := by
  rw [← hf.map_add_one', sub_add_cancel, add_comm]



/-! ##### If `f` is injective, we are done -/

section

variable (h : f.Injective)
include h

theorem map_zero_mul_self_of_injective : f 0 * f 0 = 1 :=
  h (hf.map_map_zero_mul_self.trans hf.map_one_eq_zero.symm)

theorem solution_of_injective (x) : f x = f 0 * (1 - x) := by
  have X := hf.map_map_zero_mul_map
  have h0 := X (f 0 * f x)
  rw [eq_sub_of_add_eq (X x), mul_sub, add_sub_left_comm, add_right_eq_self] at h0
  replace X := hf.map_zero_mul_self_of_injective h
  replace h0 := h (eq_of_sub_eq_zero h0)
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', X] at h0
  rw [h0, ← mul_assoc, X, one_mul]

theorem map_zero_comm_of_injective (x) : f 0 * x = x * f 0 := by
  have h0 : f 0 * f (1 - x) = f (1 - x) * f 0 := by
    apply h; rw [← add_left_inj, hf, zero_mul, add_comm 0, hf, mul_zero]
  rw [hf.solution_of_injective h (1 - x), sub_sub_cancel, mul_assoc] at h0
  replace h0 : (f 0 * f 0) * (f 0 * x) = (f 0 * f 0) * (x * f 0) := by
    rw [mul_assoc, h0, mul_assoc]
  rwa [hf.map_zero_mul_self_of_injective h, one_mul, one_mul] at h0

end

end good





/-! ### Properties of reduced good function -/

namespace ReducedGood

variable [Ring R] {f : R → R} (hf : ReducedGood f)
include hf

theorem map_eq_zero_iff : f c = 0 ↔ c = 1 :=
  ⟨λ h ↦ hf.period_imp_eq _ _ (hf.is_good.period_of_map_eq_zero h),
  λ h ↦ h ▸ hf.is_good.map_one_eq_zero⟩

theorem map_zero_mul_self : f 0 * f 0 = 1 :=
  hf.map_eq_zero_iff.mp hf.is_good.map_map_zero_mul_self

end ReducedGood
