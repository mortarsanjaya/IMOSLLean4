/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Finset.Lattice.Fold

/-!
# IMO 2007 A1 (P1)

Fix an ordered abelian group $G$ and a positive integer $n$.
Consider a sequence $(a_i)_{i = 0}^n$ of elements of $G$.
Fix an arbitrary non-decreasing sequence $(x_i)_{i = 0}^n$ in $G$, and let
$$ L = \max_{j ≤ n} |x_j - a_j|. $$
* Prove that $2L ≥ a_k - a_m$ for any $k ≤ m ≤ n$.
* Fix an arbitrary $g ∈ G$ such that $2g ≥ a_k - a_m$ for any $k ≤ m ≤ n$.
  Prove that there exists a choice of $(x_i)_{i = 1}^n$ such that $L = g$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2007SL.pdf).

### Notes

The above formulation is chosen to avoid too many layers of $\max$.
It is easy to see that for $G = ℝ$, this formulation implies the original formulation.

In our implementation, the sequences are infinite.
In part 2, we even let the whole infinite sequence be non-decreasing.
-/

namespace IMOSL
namespace IMO2007A1

open Finset

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (a : ℕ → G) (n : ℕ)

/-- Final solution, part 1 -/
theorem final_solution_part1 {x : ℕ → G} (hx : Monotone x) (h0 : k ≤ m) (h1 : m ≤ n) :
    a k - a m ≤ 2 • (range (n + 1)).sup' nonempty_range_add_one (λ i ↦ |x i - a i|) :=
  ---- The proof is just inequality bash.
  let L := (range (n + 1)).sup' nonempty_range_add_one (λ i ↦ |x i - a i|)
  calc a k - a m
  _ ≤ (a k - x k) + (x m - a m) := by
    rw [sub_add, sub_le_sub_iff_left, ← sub_add, add_le_iff_nonpos_left, sub_nonpos]
    exact le_of_eq_of_le rfl (hx h0)
  _ ≤ |(a k - x k) + (x m - a m)| := le_abs_self _
  _ ≤ |a k - x k| + |x m - a m| := abs_add_le _ _
  _ = |x k - a k| + |x m - a m| := by rw [abs_sub_comm]
  _ ≤ L + L := by
    have h2 (i) (hi : i ≤ n) : |x i - a i| ≤ L :=
      le_sup' (λ i ↦ |x i - a i|) (mem_range_succ_iff.mpr hi)
    exact add_le_add (h2 k (h0.trans h1)) (h2 m h1)
  _ = 2 • L := (two_nsmul L).symm

/-- Final solution, part 2 -/
theorem final_solution_part2 (ha : ∀ k m : ℕ, k ≤ m → m ≤ n → a k - a m ≤ 2 • g) :
    ∃ x : ℕ → G, Monotone x ∧
      (range (n + 1)).sup' nonempty_range_add_one (λ i ↦ |x i - a i|) = g := by
  ---- A working `(x_i)_{i ≥ 0}` is given by `x_n = max{a_i : i ≤ n} - g`.
  let x (i : ℕ) : G := (range (i + 1)).sup' nonempty_range_add_one a - g
  refine ⟨x, ?_, le_antisymm ?_ ?_⟩
  ---- Clearly the sequence is non-decreasing.
  · intro k m h
    refine sub_le_sub_right (sup'_le _ _ λ i hi ↦ le_sup' _ ?_) g
    rw [mem_range_succ_iff] at hi ⊢
    exact hi.trans h
  ---- First show that `max_{i ≤ n} |x_i - a_i| ≤ g`.
  · refine sup'_le _ _ λ i hi ↦ abs_le.mpr ⟨?_, ?_⟩
    -- Show that `x_i - a_i ≥ -g`.
    · rw [neg_le_sub_iff_le_add, sub_add_cancel]
      exact le_sup' _ (self_mem_range_succ i)
    -- Show that `x_i - a_i ≤ g`.
    · obtain ⟨k, hk, h⟩ :
          ∃ k ∈ range (i + 1), (range (i + 1)).sup' nonempty_range_add_one a = a k :=
        exists_mem_eq_sup' _ _
      rw [mem_range_succ_iff] at hi hk
      rw [sub_right_comm, sub_le_iff_le_add, ← two_nsmul, h]
      exact le_of_eq_of_le rfl (ha k i hk hi)
  ---- Now show that `max_{i ≤ n} |x_i - a_i| ≥ g`.
  · calc g
      _ ≤ |g| := le_abs_self _
      _ = |(range 1).sup' nonempty_range_add_one a - g - a 0| := by
        simp only [range_one]; rw [sup'_singleton, sub_sub_cancel_left, abs_neg]
      _ ≤ (range (n + 1)).sup' nonempty_range_add_one (λ i ↦ |x i - a i|) :=
        le_sup' (λ i ↦ |x i - a i|) (mem_range_succ_iff.mpr (Nat.zero_le n))
