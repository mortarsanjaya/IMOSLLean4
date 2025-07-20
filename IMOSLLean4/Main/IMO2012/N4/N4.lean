/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.Ring

/-!
# IMO 2012 N4

An integer $a$ is called *friendly* if there exists $m, n ∈ ℕ^+$ such that
$$ (m^2 + n)(n^2 + m) = a(m - n)^3. $$
1. Prove that $\{1, 2, …, 2012\}$ contains at least $500$ friendly integers.
2. Is $2$ friendly?
-/

namespace IMOSL
namespace IMO2012N4

def friendly (a : ℤ) := ∃ m > 0, ∃ n > 0, (m ^ 2 + n) * (n ^ 2 + m) = a * (m - n) ^ 3





/-! ### Part 1 -/

theorem friendly_of_four_mul_add_one (h : 0 < k) : friendly (4 * k + 1) :=
  ⟨2 * k + 1, add_pos (mul_pos two_pos h) Int.one_pos, k, h, by ring⟩

section

open scoped Classical

/-- Final solution, part 1, general version -/
theorem final_solution_part1_general (n : ℕ) :
    n ≤ ((Finset.Icc 1 (4 * n.succ : ℤ)).filter friendly).card := by
  have h : (λ k : ℕ ↦ 4 * (k.succ : ℤ) + 1).Injective := λ a b h ↦ by
    rw [add_left_inj, mul_eq_mul_left_iff, Nat.cast_inj, Nat.succ_inj] at h
    exact h.resolve_right four_ne_zero
  have h0 (a) (ha : a ∈ Finset.range n) :
      4 * (a.succ : ℤ) + 1 ∈ (Finset.Icc 1 (4 * n.succ : ℤ)).filter friendly := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_add_of_nonneg_left (mul_nonneg zero_le_four a.succ.cast_nonneg), ?_⟩,
      friendly_of_four_mul_add_one (Nat.cast_pos.mpr a.succ_pos)⟩
    rw [n.cast_succ, mul_add_one (4 : ℤ)]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le_four)
      (Int.le_add_of_nonneg_right zero_le_three)
    rw [Nat.cast_le, Nat.succ_le_iff]; exact Finset.mem_range.mp ha
  exact (Finset.card_range n).symm.trans_le (Finset.card_le_card_of_injOn _ h0 h.injOn)

/-- Final solution, part 1 -/
theorem final_solution_part1 : 500 ≤ ((Finset.Icc 1 2012).filter friendly).card :=
  (Nat.le_add_right 500 2 : 500 ≤ 502).trans (final_solution_part1_general 502)

end





/-! ### Part 2 -/

/-- Final solution, part 2 -/
theorem final_solution_part2 : ¬friendly 2 := by
  rintro ⟨m, hm, n, hn, h⟩
  have h0 : 0 < m - n := by
    replace h : 0 < (m - n) ^ 3 := by
      refine pos_of_mul_pos_right ?_ zero_le_two
      have X {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ 2 + b := add_pos (pow_pos ha 2) hb
      exact (mul_pos (X hm hn) (X hn hm)).trans_eq h
    have h0 : Odd 3 := Nat.odd_iff.mpr rfl
    exact h0.pow_pos_iff.mp h
  ---- Obtain `s` such that `(m + n - 1 + s)s = 2(m - n)`
  obtain ⟨s, h1, h2⟩ : ∃ s > 0, (m + n - 1 + s) * s = 2 * (m - n) := by
    -- First obtain `s` such that `(m + n - 1 + s)^2 = (m + n - 1)^2 + 8(m - n)`
    obtain ⟨s, h1, h2⟩ : ∃ s > 0, (m + n - 1 + s) ^ 2 = (m + n - 1) ^ 2 + 8 * (m - n) := by
      have h1 : (m ^ 2 + n + n ^ 2 + m) ^ 2 = (m - n) ^ 2 * ((m + n - 1) ^ 2 + 8 * (m - n)) :=
        calc _ = (m - n) ^ 2 * (m + n - 1) ^ 2 + 4 * ((m ^ 2 + n) * (n ^ 2 + m)) := by ring
             _ = (m - n) ^ 2 * (m + n - 1) ^ 2 + 4 * (2 * (m - n) ^ 3) := by rw [h]
             _ = _ := by rw [← mul_assoc, pow_succ _ 2, mul_left_comm, ← mul_add]; rfl
      obtain ⟨t, h2⟩ : m - n ∣ m ^ 2 + n + n ^ 2 + m :=
        (Int.pow_dvd_pow_iff (Nat.succ_ne_zero 1)).mp ⟨_, h1⟩
      rw [h2, mul_pow, mul_eq_mul_left_iff, or_iff_left (pow_ne_zero 2 h0.ne.symm)] at h1
      refine ⟨t - (m + n - 1), ?_, by rwa [add_sub_cancel]⟩
      -- It remains to show that `t > m + n - 1`
      refine Int.sub_pos.mpr (lt_of_pow_lt_pow_left₀ 2 ?_ ?_)
      · rw [← mul_nonneg_iff_right_nonneg_of_pos h0, ← h2]
        exact add_nonneg (add_nonneg (add_nonneg (sq_nonneg _) hn.le) (sq_nonneg _)) hm.le
      · rw [h1, lt_add_iff_pos_right]
        exact mul_pos (by decide) h0
    -- Now we rearrange to `(2(m + n - 1) + s)s = 8(m - n)`
    rw [← sub_eq_iff_eq_add', sq_sub_sq, add_right_comm, add_sub_cancel_left, ← two_mul] at h2
    -- Now prove that `s` is even
    obtain ⟨s, rfl⟩ : 2 ∣ s := by
      replace h2 : 2 ∣ (2 * (m + n - 1) + s) * s :=
        ⟨4 * (m - n), h2.trans (Int.mul_assoc 2 4 _)⟩
      rw [add_mul, mul_assoc, Int.dvd_add_right ⟨_, rfl⟩, ← sq, Int.dvd_iff_emod_eq_zero,
        ← Int.even_iff, Int.even_pow, Int.even_iff, ← Int.dvd_iff_emod_eq_zero] at h2
      exact h2.1
    -- Finally, get the desired `s`
    refine ⟨s, (pos_iff_pos_of_mul_pos h1).mp two_pos, ?_⟩
    have X : (8 : ℤ) = 2 * 2 * 2 := rfl
    rw [← mul_add, mul_mul_mul_comm, X, Int.mul_assoc (2 * 2), mul_eq_mul_left_iff] at h2
    exact h2.resolve_right four_ne_zero
  ---- Next, by the given estimate, prove that `s = 1`
  obtain rfl : s = 1 := by
    rw [gt_iff_lt, ← Int.add_one_le_iff, le_iff_eq_or_lt] at h1
    refine (h1.resolve_right λ (h1 : 2 ≤ s) ↦ h2.not_gt ?_).symm
    replace h2 : m - n < m + n - 1 + s := by
      apply (lt_add_of_pos_right _ (two_pos.trans_le h1)).trans'
      rw [add_sub_assoc, sub_eq_add_neg, add_lt_add_iff_left,
        neg_lt_sub_iff_lt_add, ← Int.add_one_le_iff]
      exact add_le_add hn hn
    rw [mul_comm]; exact mul_lt_mul h2 h1 two_pos (h0.trans h2).le
  ---- Finally, simplify and get contradiction
  rw [sub_add_cancel, mul_one, mul_sub, two_mul,
    eq_sub_iff_add_eq, add_assoc, add_right_inj] at h2
  apply h.not_gt; calc
    _ = 16 * n ^ 3 := by rw [← h2, add_sub_cancel_left, mul_pow, ← mul_assoc]; rfl
    _ < 27 * n ^ 3 :=
      have h3 : (16 : ℤ) < 27 := Batteries.compareOfLessAndEq_eq_lt.mp rfl
      mul_lt_mul_of_pos_right h3 (pow_pos hn 3)
    _ = m ^ 2 * m := by rw [← h2, ← one_add_mul 2 n, ← pow_succ, mul_pow]; rfl
    _ ≤ _ := mul_le_mul (Int.le_add_of_nonneg_right hn.le)
      (Int.le_add_of_nonneg_left (sq_nonneg n)) hm.le (add_nonneg (sq_nonneg _) hn.le)
