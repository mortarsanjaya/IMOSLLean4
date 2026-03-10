/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow

/-!
# IMO 2012 A3 (P2)

Let $R$ be a totally ordered commutative ring and $x_0, x_1, …, x_n ∈ R$
  (with $n ≥ 1$) be positive elements such that $x_0 x_1 … x_n = 1$.
Prove that $$ (1 + x_0)^2 (1 + x_1)^3 … (1 + x_n)^{n + 2} > (n + 2)^{n + 2}. $$

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf),
  but we avoid the given substitution, relying on Bernoulli's inequality instead.
-/

namespace IMOSL
namespace IMO2012A3

open Finset

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Let `n ≥ 2` and `a, b : R` with `a > 0`, `a + b ≥ 0`, and `b ≠ 0`.
  Then `a^n + na^{n - 1} b < (a + b)^n`. -/
theorem pow_add_mul_lt_add_pow
    {a b : R} (ha : 0 < a) (hab : 0 ≤ a + b) (hb : b ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    a ^ n + n * a ^ (n - 1) * b < (a + b) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := Nat.exists_eq_add_of_le' hn
  calc a ^ (k + 2) + (k + 2 : ℕ) * a ^ (k + 1) * b
    _ < a ^ (k + 2) + (k + 2 : ℕ) * a ^ (k + 1) * b + (k + 1 : ℕ) * a ^ k * b ^ 2 :=
      lt_add_of_pos_right _ (mul_pos (hb := sq_pos_of_ne_zero hb)
        (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos k)) (pow_pos ha k)))
    _ = (a ^ (k + 1) + (k + 1 : ℕ) * a ^ k * b) * (a + b) := by rw [Nat.cast_succ]; ring
    _ ≤ (a + b) ^ (k + 1) * (a + b) := by
      have h : 0 ≤ 2 * a + b := calc
        _ ≤ a + (a + b) := add_nonneg ha.le hab
        _ = 2 * a + b := by rw [two_mul, add_assoc]
      exact mul_le_mul_of_nonneg_right (pow_add_mul_le_add_pow ha.le h _) hab
    _ = (a + b) ^ (k + 2) := (pow_succ _ _).symm

/-- An application of Bernoulli's inequality: if `1 + x ≥ 0`,
  then `(n + 2)^{n + 2} x ≤ (n + 1)^{n + 1} (1 + x)^{n + 2}` for any `n : ℕ`. -/
theorem bernoulli_special1 {x : R} (hx : 0 ≤ 1 + x) (n : ℕ) :
    (n + 2 : ℕ) ^ (n + 2) * x ≤ (n + 1 : ℕ) ^ (n + 1) * (1 + x) ^ (n + 2) := by
  refine le_of_mul_le_mul_of_pos_left ?_ (Nat.cast_pos.mpr (Nat.succ_pos n))
  calc (n + 1 : ℕ) * ((n + 2 : ℕ) ^ (n + 2) * x)
    _ = (n + 2 : ℕ) ^ (n + 2)
        + (n + 2 : ℕ) * (n + 2 : ℕ) ^ (n + 1) * ((n + 1 : ℕ) * x - 1) := by
      rw [← pow_succ', mul_sub_one, add_sub_cancel, mul_left_comm]
    _ ≤ ((n + 2 : ℕ) + ((n + 1 : ℕ) * x - 1)) ^ (n + 2) := by
      have h : (0 : R) ≤ (n + 2 : ℕ) := Nat.cast_nonneg _
      have h0 : 0 ≤ 2 * (n + 2 : ℕ) + ((n + 1 : ℕ) * x - 1) := calc
        _ ≤ (n + 2 : ℕ) + (n + 1 : ℕ) * (1 + x) :=
          add_nonneg h (mul_nonneg (Nat.cast_nonneg _) hx)
        _ = 2 * (n + 2 : ℕ) + ((n + 1 : ℕ) * x - 1) := by
          rw [two_mul, add_assoc, add_right_inj, Nat.cast_succ (n + 1),
            add_add_sub_cancel, mul_one_add]
      exact pow_add_mul_le_add_pow h h0 (n + 2)
    _ = ((n + 1 : ℕ) * (1 + x)) ^ (n + 2) := by
      rw [Nat.cast_succ, add_add_sub_cancel, mul_one_add]
    _ = (n + 1 : ℕ) * ((n + 1 : ℕ) ^ (n + 1) * (1 + x) ^ (n + 2)) := by
      rw [mul_pow, pow_succ', mul_assoc]

/-- An application of Bernoulli's inequality: if `x ≥ -1` and `(n + 1)x ≠ 1`,
  then `(n + 2)^{n + 2} x ≤ (n + 1)^{n + 1} (1 + x)^{n + 2}` for any `n : ℕ`. -/
theorem bernoulli_special2 {x : R} (hx : 0 ≤ 1 + x) {n : ℕ} (hx0 : (n + 1 : ℕ) * x ≠ 1) :
    (n + 2 : ℕ) ^ (n + 2) * x < (n + 1 : ℕ) ^ (n + 1) * (1 + x) ^ (n + 2) := by
  ---- The proof is by redoing the proof of `bernoulli_special1`.
  have h : (0 : R) ≤ (n + 1 : ℕ) := Nat.cast_nonneg (n + 1)
  refine lt_of_mul_lt_mul_left ?_ h
  calc (n + 1 : ℕ) * ((n + 2 : ℕ) ^ (n + 2) * x)
    _ = (n + 2 : ℕ) ^ (n + 2)
        + (n + 2 : ℕ) * (n + 2 : ℕ) ^ (n + 1) * ((n + 1 : ℕ) * x - 1) := by
      rw [← pow_succ', mul_sub_one, add_sub_cancel, mul_left_comm]
    _ < ((n + 2 : ℕ) + ((n + 1 : ℕ) * x - 1)) ^ (n + 2) := by
      have h0 : 0 ≤ (n + 2 : ℕ) + ((n + 1 : ℕ) * x - 1) := by
        rw [Nat.cast_succ, add_add_sub_cancel, ← mul_one_add]
        exact mul_nonneg h hx
      exact pow_add_mul_lt_add_pow (Nat.cast_pos.mpr (Nat.succ_pos _))
        h0 (sub_ne_zero_of_ne hx0) (Nat.le_add_left 2 n)
    _ = ((n + 1 : ℕ) * (1 + x)) ^ (n + 2) := by
      rw [Nat.cast_succ, add_add_sub_cancel, mul_one_add]
    _ = (n + 1 : ℕ) * ((n + 1 : ℕ) ^ (n + 1) * (1 + x) ^ (n + 2)) := by
      rw [mul_pow, pow_succ', mul_assoc]

/-- The statement to be proved holds assuming `(k + 1) x_i ≠ 1` for some `i`. -/
theorem main_statement {x : ℕ → R} {n : ℕ}
    (hxn : ∀ i ∈ range n, 0 < x i) (hxn0 : ∃ i ∈ range n, (i + 1 : ℕ) * x i ≠ 1) :
    (n + 1 : ℕ) ^ (n + 1) * ∏ i ∈ range n, x i < ∏ i ∈ range n, (1 + x i) ^ (i + 2) := by
  have h : 0 ≤ ∏ i ∈ range n, ((i + 1 : ℕ) : R) ^ (i + 1) :=
    prod_nonneg λ i _ ↦ pow_nonneg (Nat.cast_nonneg _) _
  refine lt_of_mul_lt_mul_left ?_ h
  calc (∏ i ∈ range n, ↑(i + 1) ^ (i + 1)) * ((n + 1 : ℕ) ^ (n + 1) * ∏ i ∈ range n, x i)
    _ = (∏ i ∈ range (n + 1), ↑(i + 1) ^ (i + 1)) * ∏ i ∈ range n, x i := by
      rw [← mul_assoc, prod_range_succ]
    _ = ∏ i ∈ range n, ↑(i + 2) ^ (i + 2) * x i := by
      rw [prod_mul_distrib, prod_range_succ', Nat.cast_one, one_pow, mul_one]
    _ < ∏ i ∈ range n, ↑(i + 1) ^ (i + 1) * (1 + x i) ^ (i + 2) := by
      have h0 {i} (hi : i ∈ range n) : 0 ≤ 1 + x i := add_nonneg zero_le_one (hxn i hi).le
      exact prod_lt_prod
        (λ i hi ↦ mul_pos (pow_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) _) (hxn i hi))
        (λ i hi ↦ bernoulli_special1 (h0 hi) _)
        (hxn0.imp λ k ⟨hk, hk0⟩ ↦ ⟨hk, bernoulli_special2 (h0 hk) hk0⟩)
    _ = (∏ i ∈ range n, ↑(i + 1) ^ (i + 1)) * ∏ i ∈ range n, (1 + x i) ^ (i + 2) :=
      prod_mul_distrib

/-- Final solution -/
theorem final_solution
    {x : ℕ → R} (hn : 1 < n) (hxn : ∀ i ∈ range n, 0 < x i) (hxn0 : ∏ i ∈ range n, x i = 1) :
    (n + 1 : ℕ) ^ (n + 1) < ∏ i ∈ range n, (1 + x i) ^ (i + 2) := by
  ---- It suffices to show that `(i + 1) x_i ≠ 1` for some `i < n`.
  suffices ∃ i ∈ range n, ↑(i + 1) * x i ≠ 1 by
    calc ((n + 1 : ℕ) : R) ^ (n + 1)
    _ = (n + 1 : ℕ) ^ (n + 1) * ∏ i ∈ range n, x i := by rw [hxn0, mul_one]
    _ < ∏ i ∈ range n, (1 + x i) ^ (i + 2) := main_statement hxn this
  ---- If not, then `n! = ∏_{i < n} (i + 1) x_i = 1`.
  by_contra! h
  replace h : (∏ i ∈ range n, (i + 1 : ℕ) : R) = 1 := by
    rw [← prod_eq_one h, prod_mul_distrib, hxn0, mul_one]
  replace h : ∏ i ∈ range n, (i + 1) = 1 := by
    rwa [← Nat.cast_prod, Nat.cast_eq_one] at h
  ---- But `n > 1`, so `2 ∣ n!`; contradiction.
  have h0 : 2 ∣ ∏ i ∈ range n, (i + 1) := dvd_prod_of_mem _ (mem_range.mpr hn)
  exact Nat.not_dvd_of_pos_of_lt Nat.one_pos Nat.one_lt_two (h ▸ h0)
