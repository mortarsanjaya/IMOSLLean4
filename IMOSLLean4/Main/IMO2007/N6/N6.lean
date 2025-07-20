/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Order.Ring.Int

/-!
# IMO 2007 N6 (P5)

Fix $n > 1$, and let $a$ and $b$ be positive integers such that $nab - 1 ∣ (na^2 - 1)^2$.
Prove that $a = b$.
-/

namespace IMOSL
namespace IMO2007N6

abbrev bad_pair (n : ℤ) (a b : ℕ) := n * a * b - 1 ∣ (n * a ^ 2 - 1) ^ 2

theorem bad_pair_iff : bad_pair n a b ↔ n * a * b - 1 ∣ (a - b) ^ 2 := by
  have h : n * a * b - 1 ∣ (n * a ^ 2 - n * a * b) ^ 2 - (n * a ^ 2 - 1) ^ 2 :=
    Int.modEq_iff_dvd.mp (((Int.modEq_sub _ _).symm.sub_left _).pow 2)
  rw [bad_pair, ← dvd_iff_dvd_of_dvd_sub h, sq (a : ℤ), ← mul_assoc, ← mul_sub, mul_pow]
  refine ⟨(IsCoprime.pow_right ⟨-(1 : ℤ), b, ?_⟩).dvd_of_dvd_mul_left, λ h0 ↦ h0.mul_left _⟩
  rw [neg_one_mul, mul_comm, neg_sub, sub_add_cancel]

theorem bad_pair_comm : bad_pair n a b ↔ bad_pair n b a := by
  rw [bad_pair_iff, bad_pair_iff, ← neg_sub (a : ℤ), neg_sq, mul_right_comm]

theorem bad_pair_descent (hn : 1 < n) (ha : 0 < a) (hb : a < b) (h : bad_pair n a b) :
    ∃ c, 0 < c ∧ c < a ∧ bad_pair n a c := by
  ---- First generalize `na` and make things work
  rcases h with ⟨k, h⟩
  rw [sq (a : ℤ), ← mul_assoc] at h
  unfold bad_pair; simp only [sq (a : ℤ), ← mul_assoc]
  have ha' : 0 < (a : ℤ) := Int.natCast_pos.mpr ha
  have hb' : 0 < (b : ℤ) := Int.natCast_pos.mpr (ha.trans hb)
  replace hn : 1 < n * a :=
    hn.trans_le (le_mul_of_one_le_right (Int.one_pos.trans hn).le ha')
  generalize n * a = N at hn h ⊢; clear n
  ---- Obtain some results
  obtain ⟨c, rfl⟩ : ∃ c : ℤ, k = N * c - 1 := by
    replace h : (N * a - 1) ^ 2 ≡ (N * b - 1) * k [ZMOD N] := congrArg₂ _ h rfl
    have h0 (t) : N * t - 1 ≡ -1 [ZMOD N] :=
      (Int.modEq_iff_dvd.mpr ⟨t, sub_eq_iff_eq_add.mpr rfl⟩).symm
    replace h := (h.trans ((h0 b).mul_right _)).symm.trans ((h0 a).pow 2)
    rw [neg_one_sq, neg_one_mul, Int.modEq_iff_dvd, sub_neg_eq_add, add_comm] at h
    rcases h with ⟨c, h⟩; exact ⟨c, eq_sub_of_add_eq h⟩
  have hn' : 0 < N := Int.one_pos.trans hn
  have X {t} : 0 < N * t - 1 ↔ 0 < t :=
    ⟨λ h0 ↦ (mul_pos_iff_of_pos_left hn').mp (Int.one_pos.trans (sub_pos.mp h0)),
      λ h0 ↦ sub_pos_of_lt (hn.trans_le (le_mul_of_one_le_right hn'.le h0))⟩
  have h0 : 0 < c := by
    replace h : 0 < (N * b - 1) * (N * c - 1) := (pow_pos (X.mpr ha') 2).trans_eq h
    rwa [mul_pos_iff_of_pos_left (X.mpr hb'), X] at h
  lift c to ℕ using h0.le
  refine ⟨c, Int.natCast_pos.mp h0, ?_, Dvd.intro_left _ h.symm⟩
  ---- Now it remains to show that `c < a`
  have hNab : N * a - 1 < N * b - 1 :=
    Int.sub_lt_sub_right (mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hb) hn') _
  replace h : N * c - 1 < N * a - 1 := by
    rwa [← mul_lt_mul_iff_of_pos_left (X.mpr hb'), ← h,
      sq, mul_lt_mul_iff_of_pos_right (X.mpr ha')]
  rwa [sub_lt_sub_iff_right, mul_lt_mul_iff_of_pos_left hn', Nat.cast_lt] at h

/-- Final solution -/
theorem final_solution (hn : 1 < n) (ha : 0 < a) (hb : 0 < b) (h : bad_pair n a b) :
    a = b := by
  induction' a using Nat.strong_induction_on with a a_ih generalizing b
  obtain h0 | h0 : b ≤ a ∨ a < b := le_or_gt b a
  · exact h0.eq_or_lt.elim Eq.symm λ h0 ↦ (a_ih b h0 hb ha (bad_pair_comm.mp h)).symm
  · obtain ⟨c, hc, hc0, h1⟩ := bad_pair_descent hn ha h0 h
    exact absurd (a_ih c hc0 hc ha (bad_pair_comm.mp h1)) hc0.ne
