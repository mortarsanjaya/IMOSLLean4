/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# IMO 2012 C1

Consider $n$ nonnegative integers written in a board, say $x_1, x_2, …, x_n$.
At any time, we can do the following operation: choose two indices $i < j$ with $x_i > x_j$,
  then replace $x_j$ with $x_i$ and $x_i$ with either $x_j + 1$ or $x_i - 1$.
Prove that we can only perform finitely many operations.

### Solution

We follow and slightly modify Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf).
Note that the original formulation uses positive integers instead of nonnegative integers.
These two formulations can be easily seen as at least stronger (but actually equivalent).

### Implementation details

We model the state of the board as `Fin n → ℕ`.
Inductively, we say that a state `x : Fin n → ℕ` is *losing* if
  all states `x` can reach after an operation are losing.
In particular, `x` is losing if it cannot reach any other state.

The goal is to show that every state is losing.
Instead of considering $\sum_i i x_i$, we consider $\sum_i (i - 1) x_i$.
This modification is solely made to simplify the implementation; the proof stays the same.
-/

namespace IMOSL
namespace IMO2012C1

/-! ### States reachable by another state after one operation -/

/-- A state `y : Fin n → ℕ` is called *reachable in one operation* from `x : Fin n → ℕ`
  if there exists `i < j` with `x_j < x_i` such that `y_k = x_k` for `k ≠ i, j`,
  `y_j = x_i`, and `y_i` is equal to either `x_j + 1` or `x_i - 1`. -/
def isOneOpReachable (y x : Fin n → ℕ) :=
  ∃ i j, i < j ∧ x j < x i ∧ y j = x i ∧
    (y i = x j + 1 ∨ y i = x i - 1) ∧ (∀ k ≠ i, k ≠ j → y k = x k)

/-- If the numbers in a state `x : Fin n → ℕ` are bounded by `M`, then the numbers in any
  state `y : Fin n → ℕ` reachable in one operation from `x` is also bounded by `M`. -/
theorem isOneOpReachable.bdd_of_bdd (h : isOneOpReachable y x) (hx : ∀ k, x k ≤ M) (k) :
    y k ≤ M := by
  ---- The proof is just casework on `k`.
  rcases h with ⟨i, j, hij, hij0, h, h0, h1⟩
  obtain hki | rfl : k ≠ i ∨ k = i := ne_or_eq _ _
  ---- Case 1: `k ≠ i`.
  · obtain rfl | hkj : k = j ∨ k ≠ j := eq_or_ne _ _
    exacts [h.trans_le (hx i), (h1 k hki hkj).trans_le (hx k)]
  ---- Case 2: `k = i`.
  · rcases h0 with h0 | h0
    exacts [h0.trans_le ((hx k).trans' hij0), h0.trans_le ((Nat.sub_le _ _).trans (hx k))]

/-- Rearrangement lemma: if `a < b` and `c < d` then `ad + bc < ac + bd`. -/
theorem Nat_rearrangement_two {a b c d : ℕ} (h : a < b) (h0 : c < d) :
    a * d + b * c < a * c + b * d :=
  calc a * d + b * c
  _ = a * c + b * c + a * (d - c) := by
    rw [Nat.add_right_comm, ← Nat.mul_add, Nat.add_sub_cancel' h0.le]
  _ < a * c + b * c + b * (d - c) :=
    Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right h (Nat.sub_pos_of_lt h0)) _
  _ = a * c + b * d := by
    rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' h0.le]


open Finset
/-- If a state `x` reaches `y` in one operation, then `∑_k kx_k < ∑_k ky_k`. -/
theorem isOneOpReachable.sum_mul_lt{y x : Fin n → ℕ} (h : isOneOpReachable y x) :
    ∑ k, k * x k < ∑ k, k * y k := by
  ---- Let `i < j` with `x_j < x_i`, `y_j = x_i`, and `y_i ∈ {x_j + 1, x_i - 1}`.
  rcases h with ⟨i, j, hij, hij0, h, h0, h1⟩
  replace h1 {k} (hk : k ∈ ({i, j} : Finset _)ᶜ) : y k = x k := by
    rw [mem_compl, mem_insert, mem_singleton, not_or] at hk
    exact h1 _ hk.1 hk.2
  ---- The main inequality to check is `ix_i + jx_j < iy_i + jy_j`.
  replace h0 : x j ≤ y i :=
    h0.elim (λ h0 ↦ Nat.le_of_succ_le h0.ge)
      (λ h0 ↦ (Nat.le_sub_one_of_lt hij0).trans_eq h0.symm)
  replace h0 : i * x i + j * x j < i * y i + j * y j :=
    calc i * x i + j * x j
    _ < i * x j + j * x i := Nat_rearrangement_two hij hij0
    _ ≤ i * y i + j * x i := Nat.add_le_add_right (Nat.mul_le_mul_left _ h0) _
    _ = i * y i + j * y j := by rw [h]
  ---- The rest of the calculations is easy.
  calc ∑ k, k * x k
    _ = i * x i + j * x j + ∑ k ∉ {i, j}, k * x k := by
      rw [← sum_add_sum_compl {i, j}, sum_pair hij.ne]
    _ < i * y i + j * y j + ∑ k ∉ {i, j}, k * y k :=
      Nat.add_lt_add_of_lt_of_le h0 <| Nat.le_of_eq <|
        sum_congr rfl λ k hk ↦ congrArg (_ * ·) (h1 hk).symm
    _ = ∑ k, k * y k := by
      rw [← sum_add_sum_compl {i, j}, sum_pair hij.ne]

/-- A state `x : Fin n → ℕ` is called *losing* if
  all states `x` can reach after an operation are losing. -/
inductive isLosing : (Fin n → ℕ) → Prop where
  | of_forall_isOneOpReachable (h : ∀ y, isOneOpReachable y x → isLosing y) : isLosing x

open Finset
/-- Final solution -/
theorem final_solution (x : Fin n → ℕ) : isLosing x := by
  ---- Fix a large integer `M` greater than or equal to the `x_k`'s.
  obtain ⟨M, hM⟩ : ∃ M, ∀ i, x i ≤ M := ⟨univ.sup x, λ _ ↦ le_sup (mem_univ _)⟩
  ---- Now use strong decreasing induction on `∑_k kx_k` with ceiling `∑_k kM`.
  induction h : ∑ k, k * x k using Nat.strong_decreasing_induction generalizing x with
  | base =>
      refine ⟨∑ k : Fin n, k * M, λ m hmM x hx hxm ↦ absurd ?_ (Nat.not_le_of_lt hmM)⟩
      exact (sum_le_sum λ _ _ ↦ Nat.mul_le_mul_left _ (hx _)).trans_eq' hxm
  | step T hT =>
      refine isLosing.of_forall_isOneOpReachable λ y hyx ↦ ?_
      exact hT _ (hyx.sum_mul_lt.trans_eq' h) y (hyx.bdd_of_bdd hM) rfl
