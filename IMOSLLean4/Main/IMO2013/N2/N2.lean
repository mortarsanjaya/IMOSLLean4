/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.Parity

/-!
# IMO 2013 N2 (P1)

Prove that, for any $k, n ∈ ℕ^+$, there exist positive integers $m_1, m_2, …, m_k$ such that
$$ 1 + \frac{2^k - 1}{n} = \prod_{i = 1}^k \left(1 + \frac{1}{m_i}\right). $$

### Further directions

A possible generalization is by replacing $2^k - 1$ with an arbitrary positive integer $N$.
Then the question asks to find the smallest $k = k(N) ∈ ℕ^+$ such that there exist
  positive integers $m_1, m_2, …, m_k$ for which the above desired equality hold.
Some easy results are as follows:
* The result `good_two_mul_add_one` implies that $k(2N + 1) ≤ k(N) + 1$ for any $N ∈ ℕ^+$.
* $k(6) = 4 > ⌈\log_2 (6 + 1)⌉$.
-/

namespace IMOSL
namespace IMO2013N2

open Multiset

/-- A more general predicate: the goal is to prove `good k (2^k - 1)` -/
abbrev good (k c : ℕ) := ∀ n : ℕ, 0 < n →
  ∃ S : Multiset ℕ, card S = k ∧ (∀ m ∈ S, 0 < m) ∧
    ((n + c : ℕ) : ℚ) / n = (S.map λ (m : ℕ) ↦ ((m + 1 : ℕ) : ℚ) / m).prod

/-- General form of induction step -/
theorem good_two_mul_add_one (h : good k c) : good (k + 1) (2 * c + 1) := λ n h0 ↦ by
  rcases n.even_or_odd' with ⟨t, rfl | rfl⟩
  ---- Case 1: `n = 2t`
  · replace h0 := Nat.pos_of_mul_pos_left h0
    rcases h t h0 with ⟨T, rfl, h1, h2⟩
    have X := t.add_pos_left h0 c
    refine ⟨(2 * (t + c)) ::ₘ T, card_cons _ T,
      forall_mem_cons.mpr ⟨Nat.mul_pos (Nat.succ_pos 1) X, h1⟩, ?_⟩
    rw [map_cons, prod_cons, ← h2, ← add_assoc, ← mul_add,
      div_mul_div_comm, Nat.cast_mul, Nat.cast_mul, mul_right_comm]
    exact (mul_div_mul_right _ _ <| Nat.cast_ne_zero.mpr X.ne.symm).symm
  ---- Case 2: `n = 2t + 1`
  · have X := t.succ_pos
    rcases h (t + 1) X with ⟨T, rfl, h1, h2⟩
    refine ⟨(2 * t + 1) ::ₘ T, card_cons _ T,
      forall_mem_cons.mpr ⟨(2 * t).succ_pos, h1⟩, ?_⟩
    rw [map_cons, prod_cons, ← h2, add_add_add_comm, add_right_comm,
      add_assoc (2 * t) 1, ← Nat.mul_add_one, ← mul_add, div_mul_div_comm,
      Nat.cast_mul, Nat.cast_mul, mul_right_comm]
    exact (mul_div_mul_right _ _ <| Nat.cast_ne_zero.mpr X.ne.symm).symm

/-- Final solution -/
theorem final_solution : ∀ k : ℕ, good k (2 ^ k - 1)
  | 0 => λ n h ↦ ⟨0, rfl, λ m h ↦ absurd h (notMem_zero m), by
      rw [pow_zero, Nat.sub_self, add_zero]
      exact div_self (Nat.cast_ne_zero.mpr h.ne.symm)⟩
  | k + 1 => by
      have h := good_two_mul_add_one (final_solution k)
      have h0 := k.one_le_pow 2 (Nat.succ_pos 1)
      rwa [two_mul, add_assoc, Nat.sub_add_cancel h0, add_comm _ (2 ^ k),
        ← Nat.add_sub_assoc h0, ← two_mul, ← pow_succ'] at h
