/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Floor

/-!
# IMO 2010 A1 (P1) (Dense case)

Let $R$ and $S$ be totally ordered rings with floor.
(See mathlib's `FloorRing`.)
Find all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(⌊x⌋ y) = f(x) ⌊f(y)⌋. $$

This file solves the case where $R$ is densely ordered.
-/

namespace IMOSL
namespace IMO2010A1

variable [LinearOrderedRing R] [FloorRing R]

/-- Main definition -/
def good [LinearOrderedRing S] [FloorRing S] (f : R → S) :=
  ∀ x y : R, f (⌊x⌋ • y) = f x * ⌊f y⌋

/-- Solution for densely ordered case -/
theorem good_iff_of_DenselyOrdered [DenselyOrdered R]
    [LinearOrderedRing S] [FloorRing S] {f : R → S} :
    good f ↔ (∃ C : S, ⌊C⌋ = 1 ∧ f = λ _ ↦ C) ∨ f = 0 :=
  ---- `→`
  ⟨λ h ↦ by
    have h0 : ⌊f 0⌋ = 1 ∨ f 0 = 0 := by
      have h0 := h 0 0
      rw [zsmul_zero, ← sub_eq_zero, ← mul_one_sub, mul_eq_zero] at h0
      exact h0.symm.imp_left λ h0 ↦ Int.cast_eq_one.mp (eq_of_sub_eq_zero h0).symm
    revert h0; refine Or.imp (λ h0 ↦ ?_) (λ h0 ↦ ?_)
    -- Case 1: `⌊f(0)⌋ = 1`
    · refine ⟨f 0, h0, funext λ x ↦ ?_⟩
      rw [← zsmul_zero ⌊x⌋, h, h0, Int.cast_one, mul_one]
    -- Case 2: `f(0) = 0`
    · rcases exists_between (zero_lt_one' R) with ⟨c, hc⟩
      replace h0 : ⌊f c⌋ = 0 := by
        specialize h c c
        have h1 : ⌊c⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hc.1.le, hc.2⟩
        rw [h1, zero_zsmul, h0, zero_eq_mul] at h
        exact h.elim (λ h ↦ h ▸ Int.floor_zero) Int.cast_eq_zero.mp
      replace h0 : f (-c) = 0 := by
        specialize h (-1) c
        have h1 : ⌊(-1 : R)⌋ = -1 := by
          rw [← Int.cast_one, ← Int.cast_neg, Int.floor_intCast]
        rwa [h1, neg_one_zsmul, h0, Int.cast_zero, mul_zero] at h
      funext y; specialize h (-c) (-y)
      have h1 : ⌊-c⌋ = -1 := by
        rw [Int.floor_eq_iff, Int.cast_neg, Int.cast_one, neg_add_self]
        exact ⟨neg_le_neg hc.2.le, neg_lt_zero.mpr hc.1⟩
      rwa [h0, zero_mul, h1, neg_one_zsmul, neg_neg] at h,
  ---- `←`
  λ h ↦ h.elim
    (λ ⟨C, h, h0⟩ _ _ ↦ by rw [h0, h, Int.cast_one, mul_one])
    (λ h _ _ ↦ h ▸ (zero_mul _).symm)⟩
