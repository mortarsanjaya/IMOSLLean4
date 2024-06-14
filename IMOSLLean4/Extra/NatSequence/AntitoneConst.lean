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
-/

namespace IMOSL
namespace Extra

theorem NatSeq_antitone_imp_const {a : ℕ → ℕ} (ha : Antitone a) :
    ∃ C N : ℕ, ∀ n, a (n + N) = C := by
  by_contra h; simp only [not_exists, not_forall] at h
  replace h (C : ℕ) : ∃ N : ℕ, ∀ n, a (n + N) + C ≤ a 0 := by
    induction' C with C hC
    · exact ⟨0, λ n ↦ ha n.zero_le⟩
    · rcases hC with ⟨N, hC⟩; rcases (hC 0).lt_or_eq with h0 | h0
      · refine ⟨N, λ n ↦ h0.trans_le' (Nat.add_le_add_right (ha ?_) C)⟩
        exact Nat.add_le_add_right n.zero_le N
      · rcases h (a 0 - C) N with ⟨K, h1⟩
        rw [← h0, Nat.add_sub_cancel, Nat.zero_add] at h1
        refine ⟨K + N, λ n ↦ Nat.add_one_le_iff.mpr ?_⟩
        rw [← h0, Nat.zero_add]
        refine Nat.add_lt_add_right ((ha <| (K + N).le_add_left n).trans_lt ?_) C
        exact (ha (N.le_add_left K)).lt_of_ne h1
  rcases h (a 0).succ with ⟨N, h⟩
  exact (h 0).not_lt (Nat.lt_add_left _ (a 0).lt_succ_self)
