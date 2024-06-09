/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.Infinitesimal.Basic
import Mathlib.Algebra.Order.Floor

/-!
# Infinitesimal elements of a floor ring

Let `R` be a floor ring and `ε : R` be infinitesimal.
We show that `εr` is infinitesimal for all `r : R`.

This actually implies that the set of infinitesimals in `R` is an ideal of `R`.
However, we will not show this.
-/

namespace IMOSL
namespace Extra
namespace Infinitesimal

variable [LinearOrderedRing R] [FloorRing R] {ε : R}

theorem FloorRing_mul_left (hε : Infinitesimal ε) (r : R) : Infinitesimal (r * ε) := λ k ↦ by
  apply (hε (k * ⌈|r|⌉.natAbs)).trans_le'
  rw [abs_mul, mul_nsmul', nsmul_eq_mul ⌈|r|⌉.natAbs]
  refine nsmul_le_nsmul_right (mul_le_mul_of_nonneg_right ?_ (abs_nonneg ε)) k
  rw [← Int.cast_natCast ⌈|r|⌉.natAbs, ← Int.ceil_le]
  exact Int.le_natAbs

theorem FloorRing_mul_right (hε : Infinitesimal ε) (r : R) : Infinitesimal (ε * r) := λ k ↦ by
  apply (hε (k * ⌈|r|⌉.natAbs)).trans_le'
  rw [abs_mul, mul_nsmul', nsmul_eq_mul' |ε|]
  refine nsmul_le_nsmul_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)) k
  rw [← Int.cast_natCast ⌈|r|⌉.natAbs, ← Int.ceil_le]
  exact Int.le_natAbs

theorem FloorRing_iff_mul_left₁ : Infinitesimal ε ↔ ∀ r, r * ε < 1 :=
  ⟨λ h r ↦ (h.FloorRing_mul_left r).lt_one, λ h k ↦ by
    rcases le_total 0 ε with h0 | h0
    · rw [abs_eq_self.mpr h0, nsmul_eq_mul]; exact h _
    · rw [abs_eq_neg_self.mpr h0, nsmul_eq_mul, mul_neg, ← neg_mul]; exact h _⟩

theorem FloorRing_iff_mul_right₁ : Infinitesimal ε ↔ ∀ r, ε * r < 1 :=
  ⟨λ h r ↦ (h.FloorRing_mul_right r).lt_one, λ h k ↦ by
    rcases le_total 0 ε with h0 | h0
    · rw [abs_eq_self.mpr h0, nsmul_eq_mul']; exact h _
    · rw [abs_eq_neg_self.mpr h0, nsmul_eq_mul', neg_mul, ← mul_neg]; exact h _⟩

theorem FloorRing_iff_mul_left₂ : Infinitesimal ε ↔ ∃ α, ∀ r, r * ε < α := by
  refine FloorRing_iff_mul_left₁.trans ⟨λ h ↦ ⟨1, h⟩, λ ⟨α, h⟩ r ↦ ?_⟩
  have h0 : 0 < α := (zero_mul ε).symm.trans_lt (h 0)
  specialize h (α * r); rwa [mul_assoc, mul_lt_iff_lt_one_right h0] at h

theorem FloorRing_iff_mul_right₂ : Infinitesimal ε ↔ ∃ α, ∀ r, ε * r < α := by
  refine FloorRing_iff_mul_right₁.trans ⟨λ h ↦ ⟨1, h⟩, λ ⟨α, h⟩ r ↦ ?_⟩
  have h0 : 0 < α := (mul_zero ε).symm.trans_lt (h 0)
  specialize h (r * α); rwa [← mul_assoc, mul_lt_iff_lt_one_left h0] at h
