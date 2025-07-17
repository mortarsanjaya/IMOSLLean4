/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finite.Prod

/-!
# IMO 2017 A3

Let $S$ be a finite set, and fix some $f : S → S$.
Suppose that, for any $g : S → S$, $$f ∘ g ∘ f = g ∘ f ∘ g \implies g = f. $$
Prove that $f^2(S) = f(S)$.

### Further directions

An interesting question is to classify all such functions $f$.
Since $S$ is finite, the original question is equivalent to
  saying that $f$ is a permutation on its own image.
This is not enough; for example $f = \text{id}_S$ doesn't work if $|S| ≥ 2$.

One possible point of view is to consider the graph $G = (V, E)$ where
  $V = S^S$ and $(f, g) ∈ E$ iff $f ≠ g$ and $f ∘ g ∘ f = g ∘ f ∘ g$.
The question becomes classifying isolated points of $G$.
-/

namespace IMOSL
namespace IMO2017A3

lemma iterate_add_mul_eq {S : Type*} {f : S → S} (h : f^[n + k] = f^[n]) :
    ∀ t, f^[n + k * t] = f^[n]
  | 0 => rfl
  | t + 1 => by rw [k.mul_succ, ← Nat.add_assoc, f.iterate_add,
               iterate_add_mul_eq h t, ← f.iterate_add, h]

theorem range_iter_two_eq_of_exists_iter_eq_self
    {f : S → S} (h : 2 ≤ m) (h0 : f^[m] = f) :
    Set.range f^[2] = Set.range f := by
  apply (Set.range_comp_subset_range f f).antisymm
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  nth_rw 1 [← h0, f.iterate_add]; exact Set.range_comp_subset_range _ _

variable [Fintype S]

theorem exists_lt_iterate_eq (f : S → S) : ∃ a b, a < b ∧ f^[a] = f^[b] := by
  obtain ⟨a, b, h, h0⟩ : ∃ a b : ℕ, a ≠ b ∧ f^[a] = f^[b] :=
    Finite.exists_ne_map_eq_of_infinite _
  exact h.lt_or_gt.elim (λ h ↦ ⟨a, b, h, h0⟩) (λ h ↦ ⟨b, a, h, h0.symm⟩)

theorem exists_iterate_idempotent (f : S → S) :
    ∃ n, 0 < n ∧ f^[2 * n] = f^[n] := by
  obtain ⟨a, b, h, h0⟩ := exists_lt_iterate_eq f
  rcases Nat.exists_eq_add_of_le h.le with ⟨c, rfl⟩
  rw [Nat.lt_add_right_iff_pos] at h
  refine ⟨c * a.succ, Nat.mul_pos h a.succ_pos, ?_⟩
  rw [Nat.two_mul]; refine iterate_add_mul_eq ?_ _
  obtain ⟨k, h1⟩ := Nat.exists_eq_add_of_le
    (Nat.le_mul_of_pos_left a.succ h)
  rw [h1, Nat.add_right_comm, f.iterate_add, Nat.succ_add,
    f.iterate_succ, ← h0, ← f.iterate_succ, f.iterate_add]



/-- Final solution -/
theorem final_solution (h : ∀ g : S → S, f ∘ g ∘ f = g ∘ f ∘ g → g = f) :
    Set.range f^[2] = Set.range f := by
  rcases exists_iterate_idempotent f with ⟨n, h0, h1⟩
  refine range_iter_two_eq_of_exists_iter_eq_self
    (Nat.lt_add_of_pos_left h0) (h _ ?_)
  rw [← f.iterate_succ', ← f.iterate_add]
  change (f ∘ f^[n]) ∘ f^[2] = f^[n + 1 + n] ∘ f^[2]
  rw [Nat.succ_add, ← Nat.two_mul, f.iterate_succ' (2 * n), h1]
