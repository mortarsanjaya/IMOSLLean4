/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# IMO 2017 A1

Let $a_1, a_2, …, a_n$, and $k$ be positive integers such that $k = \sum_{j ≤ n} 1/a_j$.
Suppose that some of the $a_i$s are not equal to $1$.
Prove that, for any totally ordered commutative semiring $R$ and $x ∈ R$ positive,
$$ a_1 a_2 … a_n (x + 1)^k < (x + a_1) (x + a_2) … (x + a_n). $$
-/

namespace IMOSL
namespace IMO2017A1

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Bernoulli's inequality -/

theorem bernoulli_side_ineq {x : R} (hx : 0 ≤ x) (y : R) (n : ℕ) :
    y * (n.succ * x + y) ≤ (n * x + y) * (x + y) := by
  rw [mul_add, mul_add, add_mul, add_mul, ← add_assoc, add_le_add_iff_right, mul_comm,
    mul_assoc, mul_assoc, mul_assoc, mul_comm y, add_assoc, add_comm (x * y),
    ← add_one_mul, ← Nat.cast_succ, le_add_iff_nonneg_left, ← sq, ← nsmul_eq_mul]
  exact nsmul_nonneg (pow_nonneg hx 2) n

lemma bernoulli_ineq_aux {x y : R} (hx : 0 ≤ x) (hy : 0 ≤ y) (n) :
    y ^ n.succ * (n.succ.succ * x + y) ≤ y ^ n * (n.succ * x + y) * (x + y) := by
  rw [pow_succ, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (bernoulli_side_ineq hx y _) (pow_nonneg hy n)

theorem bernoulli_ineq {x y : R} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∀ n, y ^ n * (n.succ * x + y) ≤ (x + y) ^ n.succ := by
  refine Nat.rec ?_ λ n hn ↦ ?_
  · rw [pow_zero, one_mul, Nat.cast_one, one_mul, pow_one]
  · rw [pow_succ' (x + y), add_mul, Nat.cast_succ,
      add_one_mul, add_comm _ x, add_assoc, mul_add]
    refine add_le_add ?_ ?_
    · rw [mul_comm]; refine mul_le_mul_of_nonneg_left ?_ hx
      exact pow_le_pow_left₀ hy (le_add_of_nonneg_left hx) _
    · rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left hn hy

theorem bernoulli_ineq_strict {x y : R} (hx : 0 < x) (hy : 0 ≤ y) :
    ∀ n : ℕ, y ^ n.succ * (n.succ.succ * x + y) < (x + y) ^ n.succ.succ := by
  refine Nat.rec ?_ λ n hn ↦ ?_
  · rw [pow_one, mul_comm, add_mul, ← sq, add_sq, add_assoc]
    exact lt_add_of_pos_left _ (pow_pos hx 2)
  · apply (bernoulli_ineq_aux hx.le hy _).trans_lt
    rw [pow_succ (x + y)]
    exact mul_lt_mul_of_pos_right hn (add_pos_of_pos_of_nonneg hx hy)

theorem bernoulli_ineq_special {x : R} (h : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
    (n : R) ^ n * (x + 1) ≤ (x + n) ^ n := by
  obtain ⟨n, rfl⟩ : ∃ n' : ℕ, n = n'.succ := Nat.exists_eq_succ_of_ne_zero hn.ne.symm
  rw [pow_succ, mul_assoc, mul_add_one]
  exact bernoulli_ineq h n.succ.cast_nonneg n

theorem bernoulli_ineq_special_strict {x : R} (h : 0 < x) {n : ℕ} (hn : 1 < n) :
    (n : R) ^ n * (x + 1) < (x + n) ^ n := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := Nat.exists_eq_add_of_le' hn
  rw [pow_succ, mul_assoc, mul_add_one]
  exact bernoulli_ineq_strict h (n + 2).cast_nonneg n





/-! ### Final solution -/

open Finset

/-- Final solution -/
theorem final_solution [DecidableEq ι] {f : ι → ℕ} {I : Finset ι}
    (hfI : ∀ i ∈ I, 0 < f i) (hfI0 : ∃ i ∈ I, 1 < f i)
    {k : ℕ} (hk : ∑ i ∈ I, (f i : ℚ)⁻¹ = k) {x : R} (hx : 0 < x) :
    (∏ i ∈ I, f i : ℕ) * (x + 1) ^ k < ∏ i ∈ I, (x + f i) := by
  ---- Reduce to showing the inequality for `Π_i f(i)`th powers of both sides
  refine lt_of_pow_lt_pow_left₀ (∏ i ∈ I, f i)
    (prod_nonneg λ i _ ↦ add_nonneg hx.le (Nat.cast_nonneg _)) ?_
  ---- A small product lemma
  have h (i) (hi : i ∈ I) : f i * ∏ j ∈ I.erase i, f j = ∏ j ∈ I, f j := by
    rw [mul_comm, prod_erase_mul _ _ hi]
  ---- Replace the equality on `k`
  replace hk : ∑ i ∈ I, (∏ j ∈ I.erase i, f j) = k * ∏ i ∈ I, f i := by
    rw [← Rat.natCast_inj, Nat.cast_sum, Nat.cast_mul, ← hk, sum_mul]
    refine sum_congr rfl λ i hi ↦ ?_
    have hi0 : (f i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hfI i hi).ne.symm
    rw [eq_inv_mul_iff_mul_eq₀ hi0, ← Nat.cast_mul, h i hi]
  ---- Partial calculation, leaving one inequality behind
  calc
    _ = (∏ i ∈ I, (f i : R) ^ ∏ i ∈ I, f i) * (x + 1) ^ ∑ i ∈ I, ∏ j ∈ I.erase i, f j := by
      rw [Nat.cast_prod, mul_pow, prod_pow, hk, pow_mul]
    _ = ∏ i ∈ I, (f i : R) ^ (∏ i ∈ I, f i) * (x + 1) ^ ∏ j ∈ I.erase i, f j := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum]
    _ = ∏ i ∈ I, ((f i : R) ^ f i * (x + 1)) ^ ∏ j ∈ I.erase i, f j := by
      refine prod_congr rfl λ i hi ↦ ?_
      rw [mul_pow, ← pow_mul, h i hi]
    _ < ∏ i ∈ I, ((x + f i) ^ f i) ^ ∏ j ∈ I.erase i, f j := ?_
    _ = _ := by
      rw [← prod_pow]; refine prod_congr rfl λ i hi ↦ ?_
      rw [← pow_mul, h i hi]
  ---- Now prove the main inequality
  replace h (i) (hi : i ∈ I) : 0 < (f i : R) ^ f i * (x + 1) :=
    mul_pos (pow_pos (Nat.cast_pos.mpr (hfI i hi)) _) (add_pos hx one_pos)
  refine prod_lt_prod (λ i hi ↦ pow_pos (h i hi) _) ?_ ?_
  · intro i hi; exact pow_le_pow_left₀ (h i hi).le (bernoulli_ineq_special hx.le (hfI i hi)) _
  · rcases hfI0 with ⟨i, hi, hi0⟩
    refine ⟨i, hi, pow_lt_pow_left₀ (bernoulli_ineq_special_strict hx hi0) (h i hi).le ?_⟩
    exact prod_ne_zero_iff.mpr λ j hj ↦ (hfI j (mem_of_mem_erase hj)).ne.symm
