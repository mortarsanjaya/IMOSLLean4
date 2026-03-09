/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int

/-!
# IMO 2012 N4

An integer $a$ is called *friendly* if there exists $m, n ∈ ℕ⁺$ such that
$$ (m^2 + n)(n^2 + m) = a(m - n)^3. $$
1. Prove that $\{1, 2, …, 2012\}$ contains at least $500$ friendly integers.
2. Is $2$ friendly?

### Answer for part 2

No.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf).
We implement a stronger version of part 1: for any $N ∈ ℕ$,
  the set $\{1, 2, …, 4(N + 1)\}$ contains at least $N$ friendly integers.
-/

namespace IMOSL
namespace IMO2012N4

/-- An integer `a` is called *friendly* if there exist integers
  `m, n > 0` such that `(m^2 + n)(n^2 + m) = a(m - n)^3`. -/
def friendly (a : ℤ) := ∃ m > 0, ∃ n > 0, (m ^ 2 + n) * (n ^ 2 + m) = a * (m - n) ^ 3





/-! ### Part 1 -/

/-- If `k > 0`, then `4k + 1` is friendly. -/
theorem four_mul_add_one_is_friendly (hk : 0 < k) : friendly (4 * k + 1) :=
  have h : (0 : ℤ) ≤ 2 := Int.zero_le_ofNat 2
  ⟨2 * k + 1, Int.lt_add_one_of_le (Int.mul_nonneg h (Int.le_of_lt hk)), k, hk, by ring⟩


section

open Finset Classical

/-- There are at least `N` friendly integers in `{1, 2, …, 4(N + 1)}`. -/
theorem card_Icc_friendly (N : ℕ) : N ≤ #{a ∈ Icc 1 (4 * (N + 1)) | friendly a} :=
  calc N
  _ = #(range N) := (card_range N).symm
  _ = #((range N).image λ n ↦ 4 * ((n + 1 : ℕ) : ℤ) + 1) := by
    have h : (4 : ℤ) ≠ 0 := by decide
    have h0 : (λ n : ℕ ↦ 4 * ((n + 1 : ℕ) : ℤ) + 1).Injective := by
      intro m n h0
      rwa [Int.add_left_inj, Int.mul_eq_mul_left_iff h, Int.natCast_inj, Nat.succ_inj] at h0
    exact (card_image_of_injective _ h0).symm
  _ ≤ #{a ∈ Icc 1 (4 * (N + 1)) | friendly a} := by
    refine card_le_card (image_subset_iff.mpr λ n hnN ↦ ?_)
    replace hnN : ((n + 1 : ℕ) : ℤ) < N + 1 :=
      Int.ofNat_lt_ofNat_of_lt (Nat.succ_lt_succ (mem_range.mp hnN))
    have hn : 0 < ((n + 1 : ℕ) : ℤ) := Int.ofNat_succ_pos n
    have h : 0 < (4 : ℤ) := by decide
    have h0 : 1 ≤ 4 * ((n + 1 : ℕ) : ℤ) + 1 :=
      Int.le_add_of_nonneg_left (Int.mul_nonneg h.le hn.le)
    have h1 : 4 * ((n + 1 : ℕ) : ℤ) + 1 ≤ 4 * (N + 1) :=
      Int.add_one_le_of_lt (Int.mul_lt_mul_of_pos_left hnN h)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨h0, h1⟩, four_mul_add_one_is_friendly hn⟩

/-- Final solution, part 1 -/
theorem final_solution_part1 : 500 ≤ #{a ∈ Icc 1 2012 | friendly a} :=
  calc 500
  _ ≤ 502 := by decide
  _ ≤ #{a ∈ Icc 1 2012 | friendly a} := card_Icc_friendly 502

end





/-! ### Part 2 -/

/-- If `0 < b ≤ a` and `a^2 + 8b` is a square, then `a + 1 = 2b`. -/
theorem add_one_eq_two_mul_sq_add_eight_mul_is_square
    {a b c : ℤ} (hb : b > 0) (hba : b ≤ a) (habc : a ^ 2 + 8 * b = c ^ 2) :
    a + 1 = 2 * b := by
  have X2 : (0 : ℤ) ≤ 2 := by decide
  have X4 : (4 : ℤ) ≠ 0 := by decide
  have X8 : (0 : ℤ) < 8 := by decide
  ---- WLOG we can assume `c ≥ 0`.
  wlog hc : c ≥ 0 generalizing c
  · refine this (habc.trans (neg_sq _).symm) (Int.neg_nonneg_of_nonpos (Int.le_of_not_le hc))
  ---- Parity argument yields that `c - a` is even, say `c - a = 2d`.
  obtain ⟨d, hd⟩ : 2 ∣ c - a := by
    have h (n : ℤ) : Even (n ^ 2) ↔ Even n :=
      Int.even_pow.trans (and_iff_left (Nat.succ_ne_zero 1))
    have h0 : Even (8 : ℤ) := ⟨4, rfl⟩
    rw [← even_iff_two_dvd, Int.even_sub, ← h, ← habc, Int.even_add, h]
    exact iff_true_right (h0.mul_right b)
  replace hd : c = 2 * d + a := Int.sub_eq_iff_eq_add.mp hd
  subst hd
  ---- Since `b > 0`, we get `c - a > 0` and so `d > 0`.
  replace hc : a < 2 * d + a := by
    refine lt_of_pow_lt_pow_left₀ 2 hc ?_
    calc a ^ 2
      _ < a ^ 2 + 8 * b := Int.lt_add_of_pos_right _ (Int.mul_pos X8 hb)
      _ = (2 * d + a) ^ 2 := habc
  replace hc : 0 < d := Int.lt_of_mul_lt_mul_left ((lt_add_iff_pos_left a).mp hc) X2
  ---- Now rearranging `a^2 + 8b = c^2` gives `d(d + a) = 2b`.
  replace habc : 4 * (2 * b) = 4 * ((d + a) * d) := calc
    _ = 8 * b := (Int.mul_assoc 4 2 b).symm
    _ = (2 * d + a) ^ 2 - a ^ 2 := eq_sub_of_add_eq' habc
    _ = (2 * d + 2 * a) * (2 * d) := by
      rw [sq_sub_sq, Int.add_sub_cancel, Int.add_assoc, ← Int.two_mul]
    _ = (2 * 2) * ((d + a) * d) := by rw [← Int.mul_add, mul_mul_mul_comm]
  replace habc : 2 * b = (d + a) * d := (Int.mul_eq_mul_left_iff X4).mp habc
  ---- We have either `d = 1` or `d ≥ 2`.
  obtain rfl | hd : 1 = d ∨ d ≥ 2 := by
    rwa [Int.lt_iff_add_one_le, Int.le_iff_eq_or_lt, Int.lt_iff_add_one_le] at hc
  ---- If `d = 1`, we get what we want.
  · rwa [Int.mul_one, Int.add_comm, eq_comm] at habc
  ---- If `d = 2`, then size comparison gives contradiction.
  · refine absurd habc (Int.ne_of_lt ?_)
    calc 2 * b
      _ ≤ d * a := Int.mul_le_mul hd hba hb.le hc.le
      _ < d * d + d * a := Int.lt_add_of_pos_left _ (Int.mul_pos hc hc)
      _ = (d + a) * d := by rw [← Int.mul_add, Int.mul_comm]

/-- Final solution, part 2 -/
theorem final_solution_part2 : ¬friendly 2 := by
  ---- Suppose that `(m^2 + n)(n^2 + m) = 2(m - n)^3` for some `m, n ∈ ℕ⁺`.
  rintro ⟨m, hm, n, hn, h⟩
  ---- We first note that `m - n > 0`.
  have hmn : 0 < 2 * (m - n) ^ 3 := by
    have h0 {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ 2 + b :=
      Int.add_pos (Int.pow_pos ha) hb
    exact (Int.mul_pos (h0 hm hn) (h0 hn hm)).trans_eq h
  replace hmn : 0 < m - n := by
    have h0 : (0 : ℤ) < 2 := by decide
    have h1 : Odd 3 := by decide
    exact h1.pow_pos_iff.mp (Int.pos_of_mul_pos_right hmn h0)
  ---- Rearranging gives `(m^2 + n + n^2 + m)^2 = (m - n)^2 ((m - n - 1)^2 + 8(m - n))`.
  have h0 : (m ^ 2 + n + n ^ 2 + m) ^ 2 = (m - n) ^ 2 * ((m + n - 1) ^ 2 + 8 * (m - n)) :=
    calc  _ = (m - n) ^ 2 * (m + n - 1) ^ 2 + 4 * ((m ^ 2 + n) * (n ^ 2 + m)) := by ring
          _ = (m - n) ^ 2 * (m + n - 1) ^ 2 + 4 * (2 * (m - n) ^ 3) := by rw [h]
          _ = _ := by rw [← mul_assoc, pow_succ _ 2, mul_left_comm, ← mul_add]; rfl
  ---- In particular, `(m + n - 1)^2 + 8(m - n)` is a square.
  obtain ⟨c, h1⟩ : m - n ∣ m ^ 2 + n + n ^ 2 + m :=
    (Int.pow_dvd_pow_iff (Nat.succ_ne_zero 1)).mp ⟨_, h0⟩
  replace h0 : c ^ 2 = (m + n - 1) ^ 2 + 8 * (m - n) := by
    rwa [h1, Int.mul_pow, Int.mul_eq_mul_left_iff (Int.pow_ne_zero hmn.ne.symm)] at h0
  ---- Since `0 < m - n ≤ m + n - 1`, we get `m + n = 2(m - n)` and so `m = 3n`.
  replace h1 : m - n ≤ m + n - 1 := by
    rw [Int.le_sub_one_iff, Int.sub_lt_iff, Int.add_assoc, lt_add_iff_pos_right]
    exact Int.add_pos hn hn
  replace h0 : m + n - 1 + 1 = 2 * (m - n) :=
    add_one_eq_two_mul_sq_add_eight_mul_is_square hmn h1 h0.symm
  replace h0 : m = 3 * n := by
    rwa [Int.sub_add_cancel, Int.mul_sub, eq_sub_iff_add_eq, Int.add_assoc,
      ← one_add_mul, Int.two_mul m, Int.add_right_inj, eq_comm] at h0
  ---- But then the original equality yields `16n^3 = 27n^3`; contradiction.
  subst h0; refine Int.ne_of_gt ?_ h
  calc 2 * (3 * n - n) ^ 3
    _ = 2 * (3 - 1) ^ 3 * n ^ 3 := by rw [← sub_one_mul, Int.mul_pow, Int.mul_assoc]
    _ < 3 ^ 3 * n ^ 3 := Int.mul_lt_mul_of_pos_right (by decide) (Int.pow_pos hn)
    _ = (3 * n) ^ 2 * (3 * n) := by rw [← Int.mul_pow, Int.pow_succ]
    _ < ((3 * n) ^ 2 + n) * (n ^ 2 + 3 * n) :=
      mul_lt_mul'' (Int.lt_add_of_pos_right _ hn)
        (Int.lt_add_of_pos_left _ (Int.pow_pos hn)) (sq_nonneg _) hm.le
