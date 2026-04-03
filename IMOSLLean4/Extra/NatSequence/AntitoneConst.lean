/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Order.Monotone.Basic
import Mathlib.Order.OrderIsoNat

/-!
# Antitone sequence of naturals

Let `a : ℕ → ℕ` be an antitone sequence of natural numbers.
We show that `a` must be eventually constant.

### TODO

Delete this file once the result to be proved is up on `mathlib`.
-/

namespace IMOSL
namespace Extra

/-- An antitone sequence of natural numbers converge to a constant. -/
@[deprecated WellFoundedGT.monotone_chain_condition (since := "2026-04-03")]
theorem NatSeq_antitone_converges {a : ℕ → ℕ} (ha : Antitone a) :
    ∃ C N, ∀ n ≥ N, a n = C := by
  obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → a n = a m :=
    WellFoundedGT.monotone_chain_condition (α := ℕᵒᵈ) ⟨_, ha⟩
  exact ⟨a n, n, λ m hm ↦ (hn m hm).symm⟩

@[deprecated NatSeq_antitone_converges (since := "2025-07-17")]
theorem NatSeq_antitone_imp_const {a : ℕ → ℕ} (ha : Antitone a) :
    ∃ C N : ℕ, ∀ n, a (n + N) = C := by
  obtain ⟨C, N, h⟩ : ∃ C N, ∀ n ≥ N, a n = C := NatSeq_antitone_converges ha
  exact ⟨C, N, λ n ↦ h _ (Nat.le_add_left N n)⟩
