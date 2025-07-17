/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# IMO 2015 A1

Let $F$ be a totally ordered field.
Let $(a_n)_{n ≥ 0}$ be a sequence of positive elements of $F$ such that
  $a_{k + 1} ≥ \dfrac{(k + 1) a_k}{a_k^2 + k}$ for all $k ∈ ℕ$.
Prove that, for every $n ≥ 2$,
$$ a_0 + a_1 + … + a_{n - 1} ≥ n. $$

### Further directions

Generalize to totally ordered semirings `R` with `ExistsAddOfLE R`.

If impossible, we can alternatively generalize the above sequence to
  two sequences $(a_n)_{n ≥ 0}$, $(b_n)_{n ≥ 0}$ satisfying
  $b_{k + 1} ≤ a_k + b_k$ and $a_k b_k ≥ k$ for all $k ∈ ℕ$.
-/

namespace IMOSL
namespace IMO2015A1

open Finset

/-- Final solution -/
theorem final_solution [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {a : ℕ → F} (h : ∀ k : ℕ, 0 < a k)
    (h0 : ∀ k : ℕ, (k.succ : F) * a k / (a k ^ 2 + k) ≤ a k.succ) :
    ∀ n : ℕ, 2 ≤ n → (n : F) ≤ (range n).sum a := by
  ---- First replace the inequality condition on `a`
  replace h0 (k : ℕ) : (k.succ : F) / a k.succ ≤ a k + k / a k := by
    rw [add_div' _ _ _ (h k).ne.symm, div_le_div_iff₀ (h _) (h k), ← sq]
    exact (div_le_iff₀' <| add_pos_of_pos_of_nonneg
      (pow_pos (h k) 2) k.cast_nonneg).mp (h0 k)
  ---- Now induct on `n`, clearing the easy cases
  refine Nat.le_induction ?_ ?_
  · rw [Nat.cast_two, sum_range_succ, sum_range_one]
    specialize h0 0
    rw [Nat.cast_one, Nat.cast_zero, zero_div, add_zero] at h0
    apply (add_le_add_right h0 _).trans'
    rw [div_add' _ _ _ (h 1).ne.symm, le_div_iff₀ (h 1), ← sq]
    have h1 := two_mul_le_add_sq 1 (a 1)
    rwa [mul_one, one_pow] at h1
  · intro n h1 h2
    rw [sum_range_succ, Nat.cast_succ]
    rcases le_total 1 (a n) with h3 | h3
    · exact add_le_add h2 h3
    ---- The hard cases
    refine le_trans ?_ (add_le_add_right (?_ : (n : F) / a n ≤ _) _)
    · rw [div_add' _ _ _ (h n).ne.symm, le_div_iff₀ (h n), add_one_mul,
        ← sub_le_iff_le_add, add_sub_assoc, ← mul_one_sub,
        ← le_sub_iff_add_le', ← mul_one_sub, ← sub_nonneg, ← sub_mul]
      refine mul_nonneg (sub_nonneg.mpr (h3.trans ?_)) (sub_nonneg.mpr h3)
      exact Nat.one_le_cast.mpr (one_le_two.trans h1)
    · clear h1 h2 h3; induction' n with n n_ih
      · rw [Nat.cast_zero, sum_range_zero, zero_div]
      · rw [sum_range_succ, add_comm _ (a n)]
        refine (h0 n).trans (add_le_add_left n_ih (a n))
