/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Floor.Ring

/-!
# IMO 2010 A1 (P1)

A totally ordered

Let $R$ and $S$ be totally ordered rings with floor. (See `FloorRing`.)
Suppose that $R$ is densely ordered.
That is, for any $x < y$ in $R$, there exists $z ∈ R$ such that $x < z < y$.
Find all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(⌊x⌋ y) = f(x) ⌊f(y)⌋. $$

### Extra

It can be proved that $R$ is densely ordered if and only if it is not isomorphic to $ℤ$.
We won't prove it here, and we won't implement the $R = ℤ$ case either.

### TODO

Change the "densely ordered" condition to $R$ containing a non-integer element.
-/

namespace IMOSL
namespace IMO2010A1

/-- Final solution -/
theorem final_solution [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    [DenselyOrdered R] [Ring S] [LinearOrder S] [IsStrictOrderedRing S] [FloorRing S]
    {f : R → S} : (∀ x y : R, f (⌊x⌋ • y) = f x * ⌊f y⌋)
      ↔ (∃ C : S, ⌊C⌋ = 1 ∧ f = λ _ ↦ C) ∨ f = 0 := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  ---- `→`
  · have h0 : ⌊f 0⌋ = 1 ∨ f 0 = 0 := by
      have h0 := h 0 0
      rw [zsmul_zero, ← sub_eq_zero, ← mul_one_sub, mul_eq_zero] at h0
      exact h0.symm.imp_left λ h0 ↦ Int.cast_eq_one.mp (eq_of_sub_eq_zero h0).symm
    revert h0; refine Or.imp (λ h0 ↦ ?_) (λ h0 ↦ ?_)
    -- Case 1: `⌊f(0)⌋ = 1`
    · refine ⟨f 0, h0, funext λ x ↦ ?_⟩
      rw [← zsmul_zero ⌊x⌋, h, h0, Int.cast_one, mul_one]
    -- Case 2: `f(0) = 0`
    · obtain ⟨c, hc, hc0⟩ : ∃ c : R, 0 < c ∧ c < 1 := exists_between one_pos
      replace h0 : ⌊f c⌋ = 0 := by
        specialize h c c
        have h1 : ⌊c⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hc.le, hc0⟩
        rw [h1, zero_zsmul, h0, zero_eq_mul] at h
        exact h.elim (λ h ↦ h ▸ Int.floor_zero) Int.cast_eq_zero.mp
      replace h0 : f (-c) = 0 := by
        specialize h (-1) c
        have h1 : ⌊(-1 : R)⌋ = -1 := by
          rw [← Int.cast_one, ← Int.cast_neg, Int.floor_intCast]
        rwa [h1, neg_one_zsmul, h0, Int.cast_zero, mul_zero] at h
      funext y; specialize h (-c) (-y)
      have h1 : ⌊-c⌋ = -1 := by
        rw [Int.floor_eq_iff, Int.cast_neg, Int.cast_one, neg_add_cancel]
        exact ⟨neg_le_neg hc0.le, neg_lt_zero.mpr hc⟩
      rwa [h0, zero_mul, h1, neg_one_zsmul, neg_neg] at h
  ---- `←`
  · rcases h with ⟨C, h, h0⟩ | rfl
    · intro x y; rw [h0, h, Int.cast_one, mul_one]
    · intro _ _; exact (zero_mul _).symm
