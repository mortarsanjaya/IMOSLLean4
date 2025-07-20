/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum.NatSqrt

/-!
# IMO 2006 N1 (P4)

Determine all pairs $(x, y) ∈ ℕ × ℤ$ such that $1 + 2^x + 2^{2x + 1} = y^2$.
-/

namespace IMOSL
namespace IMO2006N1

/-! ### Extra lemmas -/

lemma sq_eq_two_pow_mul_add_one_imp {a : ℤ} (h : 2 ^ (k + 1) ∣ a ^ 2 - 1) :
    2 ^ k ∣ a - 1 ∨ 2 ^ k ∣ a + 1 := by
  have h0 : Odd a := by
    rw [← Int.odd_pow' (Nat.succ_ne_zero 1), ← Int.not_even_iff_odd,
      ← Int.even_sub_one, even_iff_two_dvd]
    exact dvd_of_mul_left_dvd h
  rw [← one_pow (M := ℤ) 2, sq_sub_sq] at h
  refine (Int.four_dvd_add_or_sub_of_odd h0 odd_one).symm.imp (λ h1 ↦ ?_) (λ h1 ↦ ?_)
  ---- Prove that if `4 ∣ a - 1`, then `2^k ∣ a - 1`
  · rcases h1 with ⟨b, h1⟩
    replace h1 : a + 1 = 2 * 2 * b + 2 := h1 ▸ (sub_add_add_cancel a 1 1).symm
    rw [h1, mul_assoc 2 2 b, ← mul_add_one 2 (2 * b), pow_succ', mul_assoc] at h
    exact (IsCoprime.mul_add_left_right isCoprime_one_right b).pow_left.dvd_of_dvd_mul_left
      (Int.dvd_of_mul_dvd_mul_left (OfNat.ofNat_ne_zero 2) h)
  ---- Prove that if `4 ∣ a + 1`, then `2^k ∣ a + 1`
  · rcases h1 with ⟨b, h1⟩
    replace h1 : a - 1 = 2 * 2 * b - 2 := h1 ▸ (add_sub_add_right_eq_sub a 1 1).symm
    rw [h1, mul_assoc 2 2 b, ← mul_sub_one, pow_succ', mul_left_comm, sub_eq_add_neg] at h
    refine (IsCoprime.mul_add_left_right ?_ b).pow_left.dvd_of_dvd_mul_right
      (Int.dvd_of_mul_dvd_mul_left (OfNat.ofNat_ne_zero 2) h)
    rw [IsCoprime.neg_right_iff]; exact isCoprime_one_right





/-! ### Start of the problem -/

def good (x : ℕ) (y : ℤ) := 2 ^ (2 * x + 1) + 2 ^ x + 1 = y ^ 2

lemma good_zero_iff : good 0 y ↔ y = 2 ∨ y = -2 := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg, eq_comm]; rfl

lemma good_four_iff : good 4 y ↔ y = 23 ∨ y = -23 := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg, eq_comm]; rfl

lemma good_neg_right (h : good x y) : good x (-y) := h.trans (neg_sq y).symm

lemma good_succ_imp_three (h : good (x + 1) y) : x = 3 := by
  wlog hy : 0 ≤ y
  · refine this (good_neg_right h) (neg_nonneg_of_nonpos (le_of_not_ge hy))
  rw [good, two_mul, (x + 1).add_right_comm, pow_add, ← add_one_mul] at h
  rcases x with _ | x
  -- First deal with the case `x = 0`
  · replace h : Int.sqrt 11 * Int.sqrt 11 = 11 :=
      (Int.exists_mul_self 11).mp ⟨y, (sq y).symm.trans h.symm⟩
    exact absurd h (by norm_num)
  -- Now solve for `(2^{x + 3} + 1) 2^{x + 2} = y^2 - 1`
  have X : (0 : ℤ) < 2 := by decide
  have X0 : (2 : ℤ) ≠ 0 := X.ne.symm
  obtain h0 | h0 : 2 ^ (x + 1) ∣ y - 1 ∨ 2 ^ (x + 1) ∣ y + 1 := by
    apply sq_eq_two_pow_mul_add_one_imp
    rw [← h, add_sub_cancel_right]
    exact Int.dvd_mul_left _ _
  ---- Case 1: `2^x` divides `y - 1`
  · rcases h0 with ⟨m, h0⟩; rw [sub_eq_iff_eq_add] at h0; subst h0
    rw [add_sq, one_pow, add_left_inj, mul_one, sq, ← add_mul, mul_comm, mul_left_comm,
      pow_succ, mul_assoc, mul_eq_mul_left_iff, or_iff_left (pow_ne_zero _ X0), pow_succ' 2 x,
      mul_assoc, ← mul_add_one (2 : ℤ), mul_assoc, mul_eq_mul_left_iff, or_iff_left X0] at h
    replace hy : 0 ≤ m := by
      rw [← Int.lt_add_one_iff, add_assoc, pow_succ', mul_assoc, one_add_one_eq_two,
        ← mul_add_one (2 : ℤ), mul_pos_iff_of_pos_left X, Int.lt_add_one_iff] at hy
      exact nonneg_of_mul_nonneg_right hy (pow_pos X x)
    change 2 ^ (x + 3) + 1 = _ at h
    -- 4 cases on `m`: `0`, `1`, `2`, and `≥ 3`
    iterate 3 rw [le_iff_eq_or_lt, ← Int.add_one_le_iff] at hy
    rcases hy with rfl | (rfl : 1 = m) | (rfl : 2 = m) | (hm : 3 ≤ m)
    · apply h.not_gt.elim
      rw [mul_zero, Int.lt_add_one_iff]
      exact pow_nonneg X.le (x + 3)
    · apply h.not_gt.elim
      rw [mul_one, mul_one, add_lt_add_iff_right]
      exact pow_right_strictMono₀ one_lt_two (Nat.lt_add_of_pos_right (Nat.succ_pos 2))
    · rw [pow_succ, ← eq_sub_iff_add_eq', ← sub_mul, mul_comm] at h
      refine absurd ⟨_, h⟩ (?_ : ¬(2 : ℤ) ∣ 1)
      exact Int.two_dvd_ne_zero.mpr rfl
    · apply h.not_lt.elim
      rw [← Int.add_one_le_iff, add_assoc, pow_add, add_one_mul _ m, mul_assoc, ← sq]
      refine add_le_add (mul_le_mul_of_nonneg_left ?_ (pow_nonneg X.le x)) ?_
      · have h0 : (2 : ℤ) ^ 3 ≤ 3 ^ 2 := Int.le_add_one (Int.le_refl 8)
        have h1 : 0 ≤ (3 : ℤ) := Int.sign_nonneg_iff.mp Int.one_nonneg
        exact h0.trans (pow_le_pow_left₀ h1 hm 2)
      · exact (Int.lt_of_add_one_le (a := 2) hm).le
  ---- Case 2: `2^x` divides `y + 1`
  · rcases h0 with ⟨m, h0⟩; rw [← eq_sub_iff_add_eq] at h0; subst h0
    rw [Int.le_sub_one_iff, mul_pos_iff_of_pos_left (pow_pos X _)] at hy
    replace h : 2 ^ x * (m ^ 2 - 2 ^ 3) = m + 1 := by
      rw [sub_sq, one_pow, add_left_inj, mul_one, sq, ← sub_mul, mul_comm, mul_left_comm,
        pow_succ, mul_assoc, mul_eq_mul_left_iff, or_iff_left (pow_ne_zero _ X0),
        pow_succ' 2 x, mul_assoc, ← mul_sub_one, mul_assoc, mul_eq_mul_left_iff,
        or_iff_left X0, sub_one_mul, ← eq_sub_iff_add_eq, sub_sub] at h
      change 2 ^ (x + 3) = 2 ^ x * m * m - (m + 1) at h
      rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', mul_assoc, ← sq, pow_add, ← mul_sub] at h
      exact h.symm
    obtain rfl : m = 3 := by
      refine ((lt_trichotomy m 3).resolve_left λ h0 ↦ ?_).resolve_right λ h0 ↦ ?_
      -- Case `m < 3`
      · refine (((add_pos hy one_pos).trans' (mul_neg_of_pos_of_neg (pow_pos X x) ?_))).ne h
        change m < 2 + 1 at h0
        have h1 : (2 ^ 2 : ℤ) < 8 := Batteries.compareOfLessAndEq_eq_lt.mp rfl
        have h2 : m ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hy.le (Int.le_of_lt_add_one h0) 2
        exact sub_neg_of_lt (h2.trans_lt h1)
      -- Case `m > 3`
      · replace h : m ^ 2 - 2 ^ 3 ∣ m + 1 := Dvd.intro_left (2 ^ x) h
        refine (Int.le_of_dvd (add_pos hy one_pos) h).not_gt ?_
        rw [lt_sub_iff_add_lt, add_assoc, sq]
        apply (mul_le_mul_of_nonneg_left (Int.add_one_le_of_lt h0) hy.le).trans_lt'
        rw [add_comm 3, mul_one_add m, add_lt_add_iff_left]
        exact mul_lt_mul_of_pos_right h0 three_pos
    change 2 ^ x * 1 = (2 ^ 2 : ℤ) at h
    rw [Int.mul_one, pow_right_inj₀ X (OfNat.one_ne_ofNat 2).symm] at h
    exact congrArg Nat.succ h

/-- Final solution -/
theorem final_solution :
    good x y ↔ (x = 0 ∧ (y = 2 ∨ y = -2)) ∨ (x = 4 ∧ (y = 23 ∨ y = -23)) := by
  rw [← good_zero_iff, ← good_four_iff]
  rcases x with _ | x
  · rw [or_iff_left λ h ↦ h.1.not_lt (Nat.succ_pos 3), and_iff_right rfl]
  · rw [or_iff_right λ h ↦ h.1.not_gt x.succ_pos, Nat.succ_inj]
    refine ⟨λ h ↦ (and_iff_left_of_imp ?_).mpr (good_succ_imp_three h), λ ⟨h, h0⟩ ↦ h ▸ h0⟩
    rintro rfl; exact h
