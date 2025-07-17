/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.BigInequalities.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Big inequalities over `Finset`

We prove some big inequalities using big operators on `Finset`.
-/

namespace IMOSL
namespace Extra

open Finset Extra

namespace Finset

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
  [DecidableEq ι]

/-! ### Cauchy-Schwarz inequality -/

/-- Cauchy-Schwarz inequality -/
theorem CauchySchwarz {f g₁ g₂ : ι → R} {S : Finset ι}
    (hg₁ : ∀ i ∈ S, 0 ≤ g₁ i) (hg₂ : ∀ i ∈ S, 0 ≤ g₂ i)
    (hf : ∀ i ∈ S, f i ^ 2 ≤ g₁ i * g₂ i) :
    S.sum f ^ 2 ≤ S.sum g₁ * S.sum g₂ := by
  induction' S using Finset.induction with i S h h0
  · rw [sum_empty, sum_empty, sq, sum_empty]
  · rw [forall_mem_insert] at hg₁ hg₂ hf
    rw [sum_insert h, sum_insert h, sum_insert h]
    exact CauchySchwarz_two hg₁.1 hg₂.1 hf.1
      (sum_nonneg hg₁.2) (sum_nonneg hg₂.2) (h0 hg₁.2 hg₂.2 hf.2)

/-- Cauchy-Schwarz inequality for universal set -/
theorem CauchySchwarz_univ [Fintype ι] {f g₁ g₂ : ι → R}
    (hg₁ : ∀ i, 0 ≤ g₁ i) (hg₂ : ∀ i, 0 ≤ g₂ i) (hf : ∀ i, f i ^ 2 ≤ g₁ i * g₂ i) :
    univ.sum f ^ 2 ≤ univ.sum g₁ * univ.sum g₂ :=
  CauchySchwarz (λ i _ ↦ hg₁ i) (λ i _ ↦ hg₂ i) (λ i _ ↦ hf i)

/-- Cauchy-Schwarz inequality, stated in the usual way -/
theorem CauchySchwarz_squares (f g : ι → R) (S : Finset ι) :
    S.sum (λ i ↦ f i * g i) ^ 2 ≤ S.sum (λ i ↦ f i ^ 2) * S.sum (λ i ↦ g i ^ 2) :=
  CauchySchwarz (λ _ _ ↦ sq_nonneg _) (λ _ _ ↦ sq_nonneg _) (λ _ _ ↦ (mul_pow _ _ 2).le)
