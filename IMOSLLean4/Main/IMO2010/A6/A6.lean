/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Order.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.WLOG

/-!
# IMO 2010 A6

Let $f, g : ℕ → ℕ$ be functions such that $f(g(x)) = f(x) + 1$
  and $g(f(x)) = g(x) + 1$ for all $x ∈ ℕ$.
Prove that $f = g$.
-/

namespace IMOSL
namespace IMO2010A6

open scoped Classical

def good (f g : ℕ → ℕ) := ∀ n : ℕ, f (g n) = (f n).succ


variable {f g : ℕ → ℕ} (h : good f g) (h0 : good g f)
include h

lemma lem1 : ∃ a, ∀ k, (∃ x, f x = k) ↔ a ≤ k := by
  have h0 : ∃ n, ∃ x, f x = n := ⟨f 0, 0, rfl⟩
  refine ⟨Nat.find h0, λ k ↦ ⟨Nat.find_min' h0, Nat.le_induction (Nat.find_spec h0) ?_ k⟩⟩
  rintro n h1 ⟨x, rfl⟩; exact ⟨g x, h x⟩

lemma lem2 (h0 : g x = g y) : f x = f y := by
  rw [← Nat.succ_inj, ← h, ← h, h0]

lemma lem3 (h0 : ∀ k, (∃ x, g x = k) ↔ a ≤ k) : a < g a :=
  (lt_or_eq_of_le <| (h0 (g a)).mp ⟨a, rfl⟩).resolve_right
    λ h1 ↦ (f a).succ_ne_self <| (h a).symm.trans (congr_arg f h1.symm)

include h0

lemma lem4 (h1 : ∃ x, f x = k) (h2 : ∃ y, f y = m) (h3 : f k = f m) : k = m := by
  rcases h1 with ⟨x, rfl⟩; rcases h2 with ⟨y, rfl⟩
  replace h3 := lem2 h0 h3
  rw [h0, h0, Nat.succ_inj] at h3
  exact lem2 h h3

lemma lem5 (h1 : ∀ k : ℕ, (∃ x, f x = k) ↔ a ≤ k)
    (h2 : ∀ k : ℕ, (∃ x, g x = k) ↔ b ≤ k) : a = b := by
  wlog h3 : a ≤ b
  · exact (this h0 h h2 h1 (le_of_not_ge h3)).symm
  refine h3.antisymm ((h2 _).mp ?_)
  obtain ⟨k, h4⟩ := Nat.exists_eq_add_of_le (lem3 h0 h1)
  obtain ⟨d, h5⟩ := (h1 (a + k)).mpr (a.le_add_right k)
  rw [Nat.succ_add, ← h5, ← h, eq_comm] at h4
  exact ⟨d, lem4 h h0 ((h1 _).mpr <| h3.trans <| (h2 _).mp ⟨d, rfl⟩)
    ((h1 a).mpr a.le_refl) h4⟩

lemma lem6 : ∃ a, (∀ k, (∃ x, f x = k) ↔ a ≤ k) ∧ (∀ k, (∃ x, g x = k) ↔ a ≤ k) :=
  (lem1 h).elim λ a h1 ↦ ⟨a, h1, (lem1 h0).elim λ _ h2 ↦ (lem5 h h0 h1 h2).symm ▸ h2⟩

lemma lem7 (h1 : ∀ k : ℕ, (∃ x, f x = k) ↔ a ≤ k)
    (h2 : ∀ k : ℕ, (∃ x, g x = k) ↔ a ≤ k) : f a = a.succ := by
  refine (Nat.succ_le_of_lt (lem3 h0 h1)).eq_or_lt'.resolve_right λ h3 ↦ ?_
  obtain ⟨t, h3⟩ := Nat.exists_eq_add_of_lt h3
  obtain ⟨x, h4⟩ := (h1 (a + t)).mpr (a.le_add_right t)
  obtain ⟨y, h5⟩ := (h1 (g x)).mpr <| (h2 _).mp ⟨x, rfl⟩
  rw [Nat.succ_add, ← h4, ← h, ← Nat.succ_eq_add_one, ← h, ← h5] at h3
  refine (lem4 h h0 ((h1 a).mpr a.le_refl) ((h1 _).mpr <| (h2 _).mp ⟨f y, rfl⟩) h3).not_lt ?_
  rw [h0, Nat.lt_succ_iff, ← h2]
  exact ⟨y, rfl⟩

/-- Final solution -/
theorem final_solution : f = g := by
  obtain ⟨a, h1, h2⟩ := lem6 h h0
  suffices h3 : ∀ n, a ≤ n → f n = n.succ ∧ g n = n.succ by
    ext x; rw [← Nat.succ_inj, ← h, (h3 _ <| (h2 _).mp ⟨x, rfl⟩).1]
  refine Nat.le_induction ⟨lem7 h h0 h1 h2, lem7 h0 h h2 h1⟩ (λ n _ h3 ↦ ⟨?_, ?_⟩)
  · rw [← Nat.succ_eq_add_one, ← h3.2, h, h3.1, h3.2]
  · rw [← Nat.succ_eq_add_one, ← h3.1, h0, h3.1, h3.2]
