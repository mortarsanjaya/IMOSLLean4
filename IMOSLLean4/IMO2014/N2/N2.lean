/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

/-
# IMO 2014 N2

Determine all pairs $(x, y)$ of integers such that
$$ 7x^2 - 13xy + y^2 = (|x - y| + 1)^3. $$
-/

namespace IMOSL
namespace IMO2014N2

def good (x y : ℤ) := 7 * x ^ 2 - 13 * x * y + 7 * y ^ 2 = (|x - y| + 1) ^ 3

lemma good_swap (h : good x y) : good y x := by
  rw [good, sub_add_comm, mul_right_comm, h, abs_sub_comm]

lemma good_iff (x y : ℤ) :
    good x y ↔ (x + y) ^ 2 = (|x - y| - 2) ^ 2 * (4 * |x - y| + 1) := by calc
  _ ↔ 7 * x ^ 2 - 13 * x * y + 7 * y ^ 2 = (|x - y| + 1) ^ 3 := Iff.rfl
  _ ↔ 4 * (7 * x ^ 2 - 13 * x * y + 7 * y ^ 2) - 27 * (x - y) ^ 2
      = 4 * (|x - y| + 1) ^ 3 - 27 * |x - y| ^ 2 := by
    rw [sq_abs, sub_left_inj, mul_left_cancel_iff_of_pos four_pos]
  _ ↔ _ := by apply Eq.congr <;> ring

lemma square_lemma (a d : ℤ) :
    a ^ 2 = (d - 2) ^ 2 * (4 * d + 1) ↔
      ∃ m, |a| = |(m ^ 2 + m - 2) * (2 * m + 1)| ∧ d = m ^ 2 + m := by
  ---- This time, resolve the `←` direction first
  refine Iff.symm ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · rcases h with ⟨m, h, rfl⟩
    rw [← sq_abs, h, sq_abs]; ring
  ---- Start by proving that `4d + 1` is a square
  obtain ⟨k, h0⟩ : ∃ k, k ^ 2 = 4 * d + 1 := by
    obtain rfl | h0 : d = 2 ∨ d - 2 ≠ 0 :=
      (eq_or_ne (d - 2) 0).imp_left (Int.eq_of_sub_eq_zero)
    · exact ⟨3, rfl⟩
    -- Focus on the case `d ≠ 2`
    obtain ⟨k, rfl⟩ : d - 2 ∣ a := (Int.pow_dvd_pow_iff (Nat.succ_ne_zero 1)).mp ⟨_, h⟩
    rw [mul_pow, Int.mul_eq_mul_left_iff (pow_ne_zero 2 h0)] at h
    exact ⟨k, h⟩
  ---- Next, prove that `k` is odd, and write `k = 2m + 1`
  obtain ⟨m, rfl⟩ : ∃ m, 2 * m + 1 = k := by
    refine ⟨k / 2, Int.two_mul_ediv_two_add_one_of_odd ?_⟩
    rw [← Int.odd_pow' (Nat.succ_ne_zero 1), h0, Int.odd_iff]
    show (2 * 2 * d + 1) % 2 = 1
    rw [Int.mul_assoc, Int.add_comm, Int.add_mul_emod_self_left, Int.one_emod_two]
  ---- Finally, show that the given choice of `m` works
  rw [← h0, ← mul_pow, sq_eq_sq_iff_abs_eq_abs] at h
  obtain rfl : d = m ^ 2 + m := by
    rw [add_sq, mul_one, one_pow, add_left_inj, mul_pow,
      ← mul_assoc, sq, ← Int.mul_add, eq_comm] at h0
    exact (Int.mul_eq_mul_left_iff four_ne_zero).mp h0
  exact ⟨m, h, rfl⟩

lemma add_eq_sub_eq_iff {a b x y : ℤ} :
    (x + y = 2 * a ∧ x - y = 2 * b) ↔ a + b = x ∧ a - b = y := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · have X {x y : ℤ} : 2 * x = 2 * y ↔ x = y :=
      Int.mul_eq_mul_left_iff (ne_of_beq_false rfl)
    refine ⟨?_, ?_⟩
    · rw [← X, Int.mul_add, ← h.1, ← h.2, add_add_sub_cancel, Int.two_mul]
    · rw [← X, Int.mul_sub, ← h.1, ← h.2, add_sub_sub_cancel, Int.two_mul]
  · rcases h with ⟨rfl, rfl⟩
    rw [add_add_sub_cancel, add_sub_sub_cancel]
    exact ⟨a.two_mul.symm, b.two_mul.symm⟩

lemma good_iff_of_y_le_x (h : y ≤ x) :
    good x y ↔ ∃ m, x = m ^ 3 + 2 * m ^ 2 - m - 1 ∧ y = m ^ 3 + m ^ 2 - 2 * m - 1 := by
  rw [good_iff, square_lemma, abs_of_nonneg (sub_nonneg_of_le h)]
  simp only [abs_eq_abs, or_and_right, ← add_eq_sub_eq_iff (a := x)]
  have X {x y : ℤ} : 2 * x = 2 * y ↔ x = y :=
    Int.mul_eq_mul_left_iff (ne_of_beq_false rfl)
  refine ⟨?_, ?_⟩; rintro ⟨m, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩
  ---- `→` direction, case `x + y = (m^2 + m - 2)(2m + 1)`
  · refine ⟨m, ?_, ?_⟩
    · rw [← X, ← h0]; ring
    · rw [← X, ← h1]; ring
  ---- `→` direction, case `x + y = -(m^2 + m - 2)(2m + 1)`
  · refine ⟨-(m + 1), ?_, ?_⟩
    · rw [← X, ← h0]; ring
    · rw [← X, ← h1]; ring
  ---- `←` direction
  · rintro ⟨m, rfl, rfl⟩
    exact ⟨m, Or.inl ⟨by ring, by ring⟩⟩

lemma special_pair_is_good (m) :
    good (m ^ 3 + 2 * m ^ 2 - m - 1) (m ^ 3 + m ^ 2 - 2 * m - 1) := by
  suffices m ^ 3 + m ^ 2 - 2 * m - 1 ≤ m ^ 3 + 2 * m ^ 2 - m - 1
    from (good_iff_of_y_le_x this).mpr ⟨m, rfl, rfl⟩
  suffices 0 ≤ m ^ 2 + m by calc
    _ ≤ (m ^ 3 + m ^ 2 - 2 * m - 1) + (m ^ 2 + m) := Int.le_add_of_nonneg_right this
    _ = m ^ 3 + 2 * m ^ 2 - m - 1 := by ring
  rw [sq, ← mul_add_one]
  obtain h | h : 0 ≤ m ∨ m < 0 := le_or_gt 0 m
  · exact Int.mul_nonneg h (Int.add_nonneg h Int.one_nonneg)
  · exact Int.mul_nonneg_of_nonpos_of_nonpos h.le h

/-- Final solution -/
theorem final_solution :
    good x y ↔ (∃ m, (x, y) = (m ^ 3 + 2 * m ^ 2 - m - 1, m ^ 3 + m ^ 2 - 2 * m - 1)) ∨
      (∃ m, (x, y) = (m ^ 3 + m ^ 2 - 2 * m - 1, m ^ 3 + 2 * m ^ 2 - m - 1)) := by
  simp only [Prod.mk.injEq]; refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · refine (le_total y x).imp (λ h0 ↦ (good_iff_of_y_le_x h0).mp h) (λ h0 ↦ ?_)
    obtain ⟨m, rfl, rfl⟩ := (good_iff_of_y_le_x h0).mp (good_swap h)
    exact ⟨m, rfl, rfl⟩
  · rcases h with ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩
    exacts [special_pair_is_good m, good_swap (special_pair_is_good m)]
