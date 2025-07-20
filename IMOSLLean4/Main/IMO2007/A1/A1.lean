/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.NatSequence.SeqMax
import Mathlib.Algebra.Order.Group.Abs

/-!
# IMO 2007 A1 (P1)

Fix an ordered abelian group $G$ and a positive integer $n$.
Consider a sequence $(a_i)_{i = 1}^n$ of elements of $G$.
Fix an arbitrary non-decreasing sequence $(x_i)_{i = 1}^n$ in $G$, and let
$$ L = \max_{j ≤ n} |x_j - a_j|. $$
* Prove that $2L \geq a_k - a_m$ for any $k ≤ m ≤ n$.
* Fix an arbitrary $g \in G$ such that $2g \geq a_k - a_m$ for any $k ≤ m ≤ n$.
  Prove that there exists a choice of $(x_i)_{i = 1}^n$ such that $L ≤ g$.

### Notes

The above formulation is chosen to avoid too many layers of $\max$.
-/

namespace IMOSL
namespace IMO2007A1

open Extra

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (a : ℕ → G) (n : ℕ)

/-- Final solution, part 1 -/
theorem final_solution_part1 {x : ℕ → G} (h : Monotone x) (h0 : k ≤ m) (h1 : m ≤ n) :
    a k - a m ≤ 2 • seqMax (λ i ↦ |x i - a i|) n := by
  apply (le_add_of_nonneg_left (sub_nonneg_of_le (h h0))).trans
  rw [← add_comm_sub, sub_add, sub_sub_sub_comm, two_nsmul]
  have X {i} : i ≤ n → |x i - a i| ≤ seqMax (λ i ↦ |x i - a i|) n :=
    le_seqMax_of_le (λ i ↦ |x i - a i|)
  exact (le_abs_self _).trans <| (abs_sub _ _).trans <| add_le_add (X h1) (X (h0.trans h1))

/-- Final solution, part 2 -/
theorem final_solution_part2 (h : ∀ k m : ℕ, k ≤ m → m ≤ n → a k - a m ≤ 2 • g) :
    ∃ x : ℕ → G, Monotone x ∧ seqMax (λ i ↦ |x i - a i|) n = g := by
  refine ⟨λ i ↦ seqMax a i - g, λ i j h0 ↦ sub_le_sub_right (seqMax_mono a h0) g, ?_⟩
  apply le_antisymm
  · rcases exists_map_eq_seqMax (λ i ↦ |seqMax a i - g - a i|) n with ⟨i, h0, h1⟩
    rw [← h1, sub_right_comm, abs_le]
    clear h1; refine ⟨?_, ?_⟩
    · rw [le_sub_iff_add_le, neg_add_cancel, sub_nonneg]
      exact le_seqMax_self a i
    · rcases exists_map_eq_seqMax a i with ⟨j, h1, h2⟩
      rw [← h2, sub_le_iff_le_add, ← two_nsmul]
      exact h j i h1 h0
  · apply (le_seqMax_of_le _ n.zero_le).trans'
    rw [sub_sub, seqMax, sub_add_cancel_right, abs_neg]
    exact le_abs_self g
