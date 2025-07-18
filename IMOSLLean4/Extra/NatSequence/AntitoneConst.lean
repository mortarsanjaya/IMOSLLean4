/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Order.Monotone.Basic

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
theorem NatSeq_antitone_converges {a : ℕ → ℕ} (ha : Antitone a) :
    ∃ C N, ∀ n ≥ N, a n = C := by
  obtain ⟨D, N, h⟩ : ∃ D N, ∀ n ≥ N, a 0 - a n = D :=
    converges_of_monotone_of_bounded (c := a 0)
      (monotone_nat_of_le_succ λ n ↦ Nat.sub_le_sub_left (ha n.le_succ) _)
      (λ n ↦ Nat.sub_le _ _)
  refine ⟨a 0 - D, N, λ n hn ↦ ?_⟩
  rw [← h n hn, Nat.sub_sub_self (ha n.zero_le)]

@[deprecated NatSeq_antitone_converges (since := "2025-07-17")]
theorem NatSeq_antitone_imp_const {a : ℕ → ℕ} (ha : Antitone a) :
    ∃ C N : ℕ, ∀ n, a (n + N) = C := by
  obtain ⟨C, N, h⟩ : ∃ C N, ∀ n ≥ N, a n = C := NatSeq_antitone_converges ha
  exact ⟨C, N, λ n ↦ h _ (Nat.le_add_left N n)⟩
