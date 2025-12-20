/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# IMO 2024 A1 (P1)

A ring with floor is a totally ordered ring $R$ with a floor function $⌊⬝⌋ : R → ℤ$
  such that for any $x ∈ R$ and $n ∈ ℤ$, we have $⌊x⌋ ≤ n ↔ x ≤ n_R$.
(See `FloorRing` for the formal definition.)

Let $R$ be an archimedean ring with floor.
Determine all $α ∈ R$ such that for any non-negative integer $n$, $n$ divides
$$ \sum_{k = 0}^n \lfloor kα \rfloor. $$

### Answer

Even integers.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2024SL.pdf),
  with a small twist.
Before proceeding into cases as in Solution 1, we assume WLOG that $-1 ≤ α < 1$.
In particular, when $⌊α⌋ = -1$, we show that $⌊nα⌋ = -1$ for all $n > 0$.
Note that the original condition assumes $n > 0$, but the case $n = 0$ is obvious.

Throughout this file, we say that $α ∈ R$ satisfying the requirement is `good`.
-/

namespace IMOSL
namespace IMO2024A1

open Finset

variable [Ring R] [LinearOrder R] [FloorRing R] [IsStrictOrderedRing R]

/-- We say that `α ∈ R` is *good* if `n ∣ ∑ k ≤ n, ⌊kα⌋` for all `n ∈ ℕ`. -/
def good (α : R) := ∀ n : ℕ, (n : ℤ) ∣ ∑ k ∈ range (n + 1), ⌊k • α⌋



/-! ### The image of even integers in `R` are good -/

/-- For any `α ∈ R` good and `N ∈ ℤ`, `α + 2N` is good. -/
lemma good.add_two_mul_int {α : R} (hα : good α) (N : ℤ) : good (α + (2 * N : ℤ)) := by
  intro n; specialize hα n
  -- The proof is just boring bash
  conv => arg 2; arg 2; ext; rw [← natCast_zsmul, zsmul_add, natCast_zsmul,
    zsmul_eq_mul, ← Int.cast_mul, Int.floor_add_intCast]
  rw [sum_add_distrib, dvd_add_right hα, ← sum_mul, ← Nat.cast_sum, ← mul_assoc,
    ← Nat.cast_two, ← Int.natCast_mul, sum_range_id_mul_two, Nat.add_sub_cancel,
    Int.natCast_mul, mul_right_comm]
  exact ⟨n.succ * N, mul_comm _ _⟩

/-- For any `α ∈ R` good and `N ∈ ℤ`, `α - 2N` is good. -/
lemma good.sub_two_mul_int {α : R} (hα : good α) (N : ℤ) : good (α - (2 * N : ℤ)) := by
  simpa only [Int.mul_neg, Int.cast_neg, sub_eq_add_neg] using hα.add_two_mul_int (-N)

/-- `0` is good. -/
lemma zero_is_good : good (0 : R) :=
  λ n ↦ ⟨0, by simp_rw [nsmul_zero]; rw [Int.floor_zero, sum_const_zero, mul_zero]⟩

/-- Any even integer, viewed as an element of `R`, is good. -/
lemma two_mul_is_good (N : ℤ) : good ((2 * N : ℤ) : R) := by
  simpa only [zero_add] using zero_is_good.add_two_mul_int (R := R) N



/-! ### A good element of `R` is an image of even integer -/

namespace good

variable [Archimedean R] {α : R} (hα : good α)
include hα

/-- The only good element `α ∈ R` with `⌊α⌋ = 0` is `α = 0`. -/
lemma zero_of_floor_eq_zero (hα0 : ⌊α⌋ = 0) : α = 0 := by
  ---- Since `α ≥ 0`, it suffices to show that `⌊nα⌋ = 0` for all `n ∈ ℕ`.
  suffices ∀ n : ℕ, ⌊n • α⌋ = 0 by
    -- We know that `α ≥ 0` since `⌊α⌋ = 0`, so now assume that `α > 0`.
    refine (Int.floor_eq_zero_iff.mp hα0).1.eq_of_not_lt' λ hα1 ↦ ?_
    -- Then `kα > 1` for some `k : ℕ` and we get a contradiction.
    obtain ⟨k, hk⟩ : ∃ k, 1 < k • α := exists_lt_nsmul hα1 _
    exact hk.asymm (Int.floor_eq_zero_iff.mp (this k)).2
  ---- Set up strong induction on `n`; assume `⌊mα⌋ = 0` for all `m < n`.
  intro n; induction n using Nat.strong_induction_on with | h n n_ih => ?_
  ---- The case `n = 0, 1` are obvious, so now write `n = k + 2`.
  cases n with | zero => rw [zero_nsmul, Int.floor_zero] | succ m => ?_
  cases m with | zero => rwa [one_nsmul] | succ k => ?_
  ---- Since `α` is good, `∑_{m ≤ k + 2} ⌊mα⌋ = ⌊(k + 2)α⌋` is divisible by `k + 2`.
  replace hα : ((k + 2 : ℕ) : ℤ) ∣ ⌊(k + 2) • α⌋ := by
    specialize hα (k + 2)
    rwa [sum_range_succ, sum_eq_zero λ m hm ↦ n_ih m (mem_range.mp hm), zero_add] at hα
  ---- Since `⌊(k + 1)α⌋ = ⌊α⌋ = 0`, we have `⌊(k + 2)α⌋ ≤ 1`.
  replace n_ih : ⌊(k + 2) • α⌋ ≤ 1 := by
    rw [succ_nsmul, ← sub_nonpos]
    apply (Int.le_floor_add_floor _ _).trans_eq
    rw [hα0, n_ih _ k.succ.lt_succ_self, Int.zero_add]
  ---- Combining the above two observation with `⌊(k + 2)α⌋ ≥ 0`, we get `⌊(k + 2)α⌋ ≤ 0`.
  refine Int.le_antisymm (Int.le_of_lt_add_one (n_ih.lt_of_ne λ hα1 ↦ ?_))
    (Int.floor_nonneg.mpr (nsmul_nonneg (Int.floor_nonneg.mp hα0.ge) _))
  rw [hα1, Int.natCast_dvd] at hα
  exact absurd (Nat.dvd_one.mp hα) k.succ_succ_ne_one

/-- There exists no good element `α ∈ R` with `⌊α⌋ = -1`. -/
lemma floor_ne_neg_one : ⌊α⌋ ≠ -1 := by
  ---- Suppose `⌊α⌋ = -1`. First write down an auxiliary statement `α < 0`.
  intro hα0; have hα1 : α < 0 := Int.floor_le_neg_one_iff.mp hα0.le
  ---- Then it suffices to show that `⌊(n + 1)α⌋ = -1` for all `n`.
  suffices ∀ n : ℕ, ⌊(n + 1) • α⌋ = -1 by
    -- Since `α < 0`, we have `kα < -1` for some `k ∈ ℕ`.
    obtain ⟨k, hk⟩ : ∃ k, k • α < -1 := exists_nsmul_lt hα1 _
    -- This `k` satisfies `⌊(k + 1)α⌋ < -1`.
    apply (this k).not_lt
    rw [Int.floor_lt, succ_nsmul, Int.cast_neg, Int.cast_one, ← add_zero (-1)]
    exact add_lt_add hk hα1
  ---- Set up strong induction on `n`; assume `⌊(m + 1)α⌋ = -1` for all `m < n`.
  intro n; induction n using Nat.strong_induction_on with | h n n_ih => ?_
  ---- The case `n = 0` is obvious, so now write `n = k + 1`.
  cases n with | zero => rwa [one_nsmul] | succ k => ?_
  ---- Since `α` is good, we have `k + 2 ∣ ∑_{m ≤ k + 2} ⌊mα⌋ + (k + 2) = ⌊(k + 2)α⌋ + 1`.
  replace hα : ((k + 2 : ℕ) : ℤ) ∣ ⌊(k + 2) • α⌋ + 1 := by
    convert dvd_add_self_right.mpr (hα (k + 2)) using 1
    -- There is no way to avoid tons of bash here...
    rw [Nat.cast_succ, ← add_assoc, add_left_inj, sum_range_succ, add_right_comm,
      right_eq_add, sum_range_succ', zero_nsmul, Int.floor_zero, add_zero,
      sum_congr rfl λ m hm ↦ n_ih m (mem_range.mp hm), sum_const, card_range,
      neg_nsmul, nsmul_one, neg_add_cancel]
  ---- Since `⌊(k + 1)α⌋ = ⌊α⌋ = -1`, we have `⌊(k + 2)α⌋ ≥ -2`.
  replace n_ih : -2 ≤ ⌊(k + 2) • α⌋ := calc
    _ = ⌊(k + 1) • α⌋ + ⌊α⌋ := congrArg₂ (· + ·) (n_ih k k.lt_succ_self).symm hα0.symm
    _ ≤ ⌊(k + 1) • α + α⌋ := Int.le_floor_add _ _
    _ = ⌊(k + 2) • α⌋ := by rw [succ_nsmul α (k + 1)]
  ---- Combining the above two observation with `⌊(k + 2)α⌋ ≤ -1`, we get `⌊(k + 2)α⌋ ≤ 0`.
  refine Int.le_antisymm (Int.floor_le_neg_one_iff.mpr (nsmul_neg hα1 k.succ.succ_ne_zero))
    (Int.add_one_le_of_lt (n_ih.lt_of_ne λ hα2 ↦ ?_))
  rw [← hα2, Int.natCast_dvd] at hα
  exact absurd (Nat.dvd_one.mp hα) k.succ_succ_ne_one

/-- The good elements are the image of even numbers in `R`. -/
lemma eq_two_mul_int : ∃ N : ℤ, α = (2 * N : ℤ) := by
  ---- Split into two cases based on the parity of `⌊α⌋`.
  obtain ⟨N, hN | hN⟩ : ∃ N, ⌊α⌋ = 2 * N ∨ ⌊α⌋ = 2 * N + 1 := Int.even_or_odd' ⌊α⌋
  ---- Case 1: `⌊α⌋ = 2N`.
  · -- Then `α - 2N` is good and `⌊α - 2N⌋ = 0`, so `α = 2N`.
    replace hα : good (α - (2 * N : ℤ)) := hα.sub_two_mul_int N
    replace hα0 : ⌊α - (2 * N : ℤ)⌋ = 0 := by
      rw [Int.floor_sub_intCast, hN, Int.sub_self]
    exact ⟨N, eq_of_sub_eq_zero (hα.zero_of_floor_eq_zero hα0)⟩
  ---- Case 2: `⌊α⌋ = 2N + 1`.
  · -- Then `α - 2N` is good and `⌊α - 2(N + 1)⌋ = -1`; impossible!
    replace hα : good (α - (2 * (N + 1) : ℤ)) := hα.sub_two_mul_int (N + 1)
    replace hα0 : ⌊α - (2 * (N + 1) : ℤ)⌋ = -1 := by
      rw [Int.floor_sub_intCast, hN, Int.mul_add, add_sub_add_left_eq_sub]; rfl
    exact absurd hα0 hα.floor_ne_neg_one

end good



/-! ### Summary -/

/-- Final solution -/
theorem final_solution [Archimedean R] {α : R} : good α ↔ ∃ N : ℤ, α = (2 * N : ℤ) :=
  ⟨good.eq_two_mul_int, λ ⟨N, hN⟩ ↦ hN ▸ two_mul_is_good N⟩
