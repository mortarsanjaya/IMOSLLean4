/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow

/-!
# IMO 2017 A1

Let $a_1, a_2, …, a_n$, and $k$ be positive integers such that $k = \sum_{j ≤ n} 1/a_j$.
Let $M = a_1 a_2 … a_n$, and suppose that $M > 1$.
Prove that for any $x ∈ ℝ$ with $x > 0$,
$$ M (x + 1)^k ≠ (x + a_1) (x + a_2) … (x + a_n). $$

### Solution

We follow and modify Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2017SL.pdf).
Instead of working over $ℝ$, we work over arbitrary ordered commutative rings.
We will need all exponents we work with to be natural numbers,
  so we also need to raise the power of both sides by $M$.
In addition, we use Bernoulli's inequality in place of the AM-GM inequality.
-/

namespace IMOSL
namespace IMO2017A1

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Let `n ≥ 2` and `a, b : R` with `a, b > 0`.
  Then `a^n + na^{n - 1} b < (a + b)^n`. -/
theorem pow_add_mul_lt_add_pow
    {a b : R} (ha : a > 0) (hb : b > 0) {n : ℕ} (hn : n ≥ 2) :
    a ^ n + n * a ^ (n - 1) * b < (a + b) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := Nat.exists_eq_add_of_le' hn
  have hab : a + b ≥ 0 := add_nonneg ha.le hb.le
  have hb0 : b ^ 2 > 0 := pow_pos hb 2
  have hab0 : 0 ≤ 2 * a + b := calc
    _ ≤ a + (a + b) := add_nonneg ha.le hab
    _ = 2 * a + b := by rw [two_mul, add_assoc]
  calc a ^ (k + 2) + (k + 2 : ℕ) * a ^ (k + 1) * b
    _ < a ^ (k + 2) + (k + 2 : ℕ) * a ^ (k + 1) * b + (k + 1 : ℕ) * a ^ k * b ^ 2 :=
      lt_add_of_pos_right _ (mul_pos (hb := hb0)
        (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos k)) (pow_pos ha k)))
    _ = (a ^ (k + 1) + (k + 1 : ℕ) * a ^ k * b) * (a + b) := by rw [Nat.cast_succ]; ring
    _ ≤ (a + b) ^ (k + 1) * (a + b) :=
      mul_le_mul_of_nonneg_right (ha := hab)
        (pow_add_mul_le_add_pow_of_sq_nonneg ha.le hb0.le (pow_nonneg hab 2) hab0 _)
    _ = (a + b) ^ (k + 2) := (pow_succ _ _).symm

/-- Let `n` be a positive integer and `x : R` with `x ≥ 0`.
  Then we have `n^n (x + 1) ≤ (x + n)^n`. -/
theorem bernoulli_special1 {x : R} (hx : x ≥ 0) {n : ℕ} (hn : n ≠ 0) :
    (n : R) ^ n * (x + 1) ≤ (x + n) ^ n :=
  calc (n : R) ^ n * (x + 1)
  _ = (n : R) ^ n + n * n ^ (n - 1) * x := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), mul_add_one, add_comm]
  _ ≤ (n + x) ^ n := by
    have hn0 : 0 ≤ (n : R) := Nat.cast_nonneg n
    have hnx : 0 ≤ n + x := add_nonneg hn0 hx
    have hnx0 : 0 ≤ 2 * n + x := add_nonneg (mul_nonneg zero_le_two hn0) hx
    exact pow_add_mul_le_add_pow_of_sq_nonneg hn0 (pow_nonneg hx 2) (pow_nonneg hnx _) hnx0 _
  _ = (x + n) ^ n := congrArg (· ^ n) (add_comm _ _)

/-- Let `n > 1` be an integer and `x : R` with `x > 0`.
  Then we have `n^n (x + 1) < (x + n)^n`. -/
theorem bernoulli_special2 {x : R} (hx : x > 0) {n : ℕ} (hn : n > 1) :
    (n : R) ^ n * (x + 1) < (x + n) ^ n := by
  have hn0 : n > 0 := Nat.zero_lt_of_lt hn
  calc (n : R) ^ n * (x + 1)
    _ = (n : R) ^ n + n * n ^ (n - 1) * x := by
      rw [← pow_succ', Nat.sub_add_cancel hn0, mul_add_one, add_comm]
    _ < (n + x) ^ n := pow_add_mul_lt_add_pow (Nat.cast_pos.mpr hn0) hx hn
    _ = (x + n) ^ n := congrArg (· ^ n) (add_comm _ _)


open Finset

/-- The "main" statement: if any of the `a_i`'s are greater than `1`,
  then `M (x + 1)^k < (x + a_1) (x + a_2) … (x + a_n)`. -/
theorem main_statement [DecidableEq ι] {a : ι → ℕ} {I : Finset ι}
    (ha : ∃ i ∈ I, a i > 1) {k : ℕ} (hk : ∑ i ∈ I, (a i : ℚ)⁻¹ = k) {x : R} (hx : x > 0) :
    (∏ i ∈ I, a i : ℕ) * (x + 1) ^ k < ∏ i ∈ I, (x + a i) := by
  set M : ℕ := ∏ i ∈ I, a i
  have hxa : ∏ i ∈ I, (x + a i) > 0 :=
    prod_pos λ i _ ↦ add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg _)
  ---- If `M = ∏_{i ∈ I} a_i` is zero, then we are done, so suppose they are not.
  obtain ha0 | ha0 : M = 0 ∨ M ≠ 0 := eq_or_ne _ _
  · rwa [ha0, Nat.cast_zero, zero_mul]
  ---- Now raise both sides to the power of `∏_{i ∈ I} a_i`.
  suffices (M * (x + 1) ^ k) ^ M < (∏ i ∈ I, (x + a i)) ^ M
    from lt_of_pow_lt_pow_left₀ _ hxa.le this
  ---- Since `∏_{i ∈ I} a_i ≠ 0`, we have `a_i > 0` for all `i ∈ I`.
  replace ha0 (i) (hi : i ∈ I) : a i ≠ 0 := prod_ne_zero_iff.mp ha0 i hi
  ---- The given equality on `k` can be rephrased as `∑_i ∏_{j ≠ i} a_j = k ∏_i a_i`.
  replace hk : ∑ i ∈ I, (∏ j ∈ I.erase i, a j) = k * M := by
    suffices ∀ i ∈ I, ((∏ j ∈ I.erase i, a j : ℕ) : ℚ) = (a i : ℚ)⁻¹ * M by
      rw [← Rat.natCast_inj, Nat.cast_sum, Nat.cast_mul, ← hk, sum_mul, sum_congr rfl this]
    intro i hi; have hi0 : (a i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ha0 i hi)
    rw [eq_inv_mul_iff_mul_eq₀ hi0, ← Nat.cast_mul, mul_prod_erase _ _ hi]
  /- From Bernoulli's inequality, we have `0 < a_i^{a_i} (x + 1) ≤ (x + a_i)^{a_i}`
    for all `i ∈ I` with the inequality being strict for at least one `i ∈ I`.
    Raise all sides to the power of `∏_{j ≠ i} a_j`. -/
  have X (i) (hi : i ∈ I) (r : R) : (r ^ a i) ^ ∏ j ∈ I.erase i, a j = r ^ M := by
    rw [← pow_mul, mul_prod_erase _ _ hi]
  have hxa0 (i) (hi : i ∈ I) : a i ^ a i * (x + 1) > 0 :=
    have hai : a i > 0 := Nat.pos_of_ne_zero (ha0 i hi)
    mul_pos (pow_pos (Nat.cast_pos.mpr hai) _) (add_pos hx one_pos)
  have hxa1 (i) (hi : i ∈ I) : a i ^ M * (x + 1) ^ ∏ j ∈ I.erase i, a j ≤ (x + a i) ^ M := by
    rw [← X i hi, ← X i hi, ← mul_pow]
    exact pow_le_pow_left₀ (hxa0 i hi).le (bernoulli_special1 hx.le (ha0 i hi)) _
  have hxa2 : ∃ i ∈ I, a i ^ M * (x + 1) ^ ∏ j ∈ I.erase i, a j < (x + a i) ^ M := by
    rcases ha with ⟨i₀, hi₀, hai₀⟩
    refine ⟨i₀, hi₀, ?_⟩
    rw [← X i₀ hi₀, ← X i₀ hi₀, ← mul_pow]
    exact pow_lt_pow_left₀ (bernoulli_special2 hx hai₀) (hxa0 _ hi₀).le
      (prod_ne_zero_iff.mpr λ j hj ↦ (ha0 j (mem_of_mem_erase hj)))
  replace hxa0 (i) (hi : i ∈ I) : a i ^ M * (x + 1) ^ ∏ j ∈ I.erase i, a j > 0 := by
    rw [← X i hi, ← mul_pow]
    exact pow_pos (hxa0 i hi) _
  clear X
  ---- Now do the main calculations.
  calc (M * (x + 1) ^ k) ^ M
    _ = ∏ i ∈ I, (a i ^ M * (x + 1) ^ ∏ j ∈ I.erase i, a j) := by
      rw [mul_pow, Nat.cast_prod, ← pow_mul, ← hk,
        ← prod_pow_eq_pow_sum, prod_mul_distrib, prod_pow]
    _ < ∏ i ∈ I, (x + a i) ^ M := prod_lt_prod hxa0 hxa1 hxa2
    _ = (∏ i ∈ I, (x + a i)) ^ M := prod_pow _ _ _

/-- Final solution -/
theorem final_solution [DecidableEq ι] {a : ι → ℕ} {I : Finset ι}
    (ha : ∏ i ∈ I, a i > 1) {k : ℕ} (hk : ∑ i ∈ I, (a i : ℚ)⁻¹ = k) {x : R} (hx : x > 0) :
    (∏ i ∈ I, a i : ℕ) * (x + 1) ^ k ≠ ∏ i ∈ I, (x + a i) := by
  refine (main_statement ?_ hk hx).ne
  contrapose! ha; exact prod_le_one' ha
