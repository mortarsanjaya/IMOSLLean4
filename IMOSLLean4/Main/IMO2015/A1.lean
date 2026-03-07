/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# IMO 2015 A1

Let $F$ be a totally ordered field.
Let $(a_n)_{n ≥ 0}$ be a sequence of positive elements of $F$ such that for any $k ∈ ℕ$,
$$ a_{k + 1} ≥ \frac{(k + 1) a_k}{a_k^2 + k}. $$
Prove that for every $n ≥ 2$,
$$ a_0 + a_1 + … + a_{n - 1} ≥ n. $$

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2015SL.pdf).
-/

namespace IMOSL
namespace IMO2015A1

open Finset

/-
/-- If `a, b ≥ 0` and `r^2 ≤ ab`, then `2r ≤ a + b`. -/
theorem two_mul_le_add_of_sq_le_mul
    [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
    {a b r : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : r ^ 2 ≤ a * b) : 2 * r ≤ a + b := by
  refine nonneg_le_nonneg_of_sq_le_sq (add_nonneg ha hb) ?_
  calc 2 * r * (2 * r)
    _ = 4 * r ^ 2 := by rw [mul_mul_mul_comm, two_mul, two_add_two_eq_four, sq]
    _ ≤ 4 * (a * b) := mul_le_mul_of_nonneg_left hr (zero_le_four)
    _ = 4 * a * b := (mul_assoc _ _ _).symm
    _ ≤ (a + b) ^ 2 := four_mul_le_pow_two_add a b
    _ = (a + b) * (a + b) := sq _
-/

/-- A version of the statement to be proved that is free of division. -/
theorem general_result
    [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
    {a b : ℕ → R} (ha : ∀ k, a k > 0) (hb : ∀ k, b k ≥ 0)
    (hab : ∀ k, b (k + 1) ≤ a k + b k) (hab0 : ∀ k, a k * b k = k)
    (hn : n ≥ 2) : n ≤ ∑ i ∈ range n, a i := by
  have hb0 : b 0 = 0 :=
    (mul_eq_zero_iff_left (ha 0).ne.symm ).mp ((hab0 0).trans Nat.cast_zero)
  ---- We use induction on `n`; the base case `n = 2` follows by AM-GM.
  induction n, hn using Nat.le_induction with | base => ?_ | succ n hn n_ih => ?_
  · calc (2 : R)
    _ = 2 * 1 := (mul_one _ ).symm
    _ ≤ a 1 + b 1 :=
      have h : 1 ^ 2 = a 1 * b 1 := by rw [hab0, Nat.cast_one, one_pow]
      two_mul_le_add_of_sq_eq_mul (ha _).le (hb _) h
    _ ≤ a 1 + (a 0 + b 0) := add_le_add_right (hab 0) _
    _ = a 0 + a 1 := by rw [hb0, add_zero, add_comm]
    _ = ∑ i ∈ range 2, a i := by rw [sum_range_succ, sum_range_one]
  ---- For the induction step, let `T = ∑_i a_i` and note the goal is `n + 1 ≤ T + a_n`.
  set T : R := ∑ i ∈ range n, a i
  calc ((n + 1 : ℕ) : R)
    _ = n + 1 := Nat.cast_succ _
    _ ≤ T + a n := ?_
    _ = ∑ i ∈ range (n + 1), a i := (sum_range_succ a n).symm
  ---- The case `a_n ≥ 1` is trivial, so assume `a_n ≤ 1`.
  obtain hn0 | hn0 : a n ≥ 1 ∨ a n ≤ 1 := le_total _ _
  · exact add_le_add n_ih hn0
  ---- Now the only part of the induction hypothesis that we need is `T ≥ 1`.
  replace n_ih : 1 ≤ T := n_ih.trans' (Nat.one_le_cast.mpr (Nat.one_le_of_lt hn))
  ---- Since `a_n ≤ 1`, we can write `a_n + c = 1` for some `c ≥ 0`.
  obtain ⟨c, hc, hc0⟩ : ∃ c ≥ 0, a n + c = 1 := exists_nonneg_add_of_le hn0
  ---- Next notice that `b_k ≤ ∑_{i < k} a_i` for all `k`, and so `b_n ≤ T`.
  replace hab (k) : b k ≤ ∑ i ∈ range k, a i := by
    induction k with | zero => rw [hb0, sum_range_zero] | succ k k_ih => ?_
    calc b (k + 1)
      _ ≤ a k + b k := hab k
      _ ≤ a k + ∑ i ∈ range k, a i := add_le_add_right k_ih _
      _ = ∑ i ∈ range (k + 1), a i := (sum_range_succ_comm a k).symm
  replace hab : b n ≤ T := hab n
  ---- Now we are ready to do the desired calculation.
  calc (n : R) + 1
    _ = a n * b n + c + a n := by rw [hab0, add_assoc, add_comm c, hc0]
    _ ≤ a n * T + c * T + a n :=
      add_le_add_left (a := a n) <| add_le_add
        (mul_le_mul_of_nonneg_left hab (ha n).le) (le_mul_of_one_le_right hc n_ih)
    _ = T + a n := by rw [← add_mul, hc0, one_mul]

/-- Final solution -/
theorem final_solution
    [Semifield F] [LinearOrder F] [IsStrictOrderedRing F] [ExistsAddOfLE F] {a : ℕ → F}
    (ha : ∀ k, a k > 0) (ha0 : ∀ k, (k + 1 : ℕ) * a k / (a k ^ 2 + k) ≤ a (k + 1))
    (hn : n ≥ 2) : n ≤ ∑ i ∈ range n, a i := by
  replace ha0 (k) : (k + 1 : ℕ) / a (k + 1) ≤ a k + k / a k := by
    have h : a k ^ 2 + ↑k > 0 := add_pos_of_pos_of_nonneg (pow_pos (ha k) 2) k.cast_nonneg'
    rw [add_div' _ _ _ (ha k).ne.symm, div_le_div_iff₀ (ha _) (ha k), ← sq, ← div_le_iff₀' h]
    exact ha0 k
  exact general_result (b := λ k ↦ k / a k) ha (λ k ↦ div_nonneg k.cast_nonneg' (ha k).le)
    ha0 (λ k ↦ mul_div_cancel₀ _ (ha k).ne.symm) hn
