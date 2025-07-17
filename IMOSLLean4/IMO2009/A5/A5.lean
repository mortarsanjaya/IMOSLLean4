/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Defs

/-!
# IMO 2009 A5

Let $R$ be a totally ordered ring.
Prove that there does not exist a function $f : R → R$ such that for all $x, y ∈ R$,
$$ f(x - f(y)) ≤ y f(x) + x. $$
-/

namespace IMOSL
namespace IMO2009A5

/-- Final solution -/
theorem final_solution [Ring R] [LinearOrder R] [IsStrictOrderedRing R] (f : R → R) :
    ¬∀ x y, f (x - f y) ≤ y * f x + x := by
  intro hf
  have hf1 (t) : f t ≤ t + f 0 := by
    specialize hf (t + f 0) 0; rwa [zero_mul, zero_add, add_sub_cancel_right] at hf
  have hf2 (y) (hy : 0 < y) : -1 - f 0 ≤ f y := by
    replace hf := (hf (f y) y).trans (add_le_add_left (hf1 y) _)
    rw [sub_self, ← add_assoc, le_add_iff_nonneg_left, ← mul_add_one y,
      mul_nonneg_iff_of_pos_left hy, ← neg_le_iff_add_nonneg] at hf
    exact sub_le_iff_le_add.mpr (hf.trans (hf1 _))
  ---- Prove that `f(x)` is "small", if it is positive
  replace hf2 (z) (hz : 0 ≤ z) (x) : z * f x ≤ 1 := by
    refine (lt_or_ge 0 (f x)).elim (λ h ↦ ?_)
      (λ h ↦ (mul_nonpos_of_nonneg_of_nonpos hz h).trans zero_le_one)
    replace hf (y) : -1 - f 0 ≤ y * f x + x := by
      obtain ⟨C, h0, h1⟩ : ∃ C, C ≤ y ∧ f C < x := by
        refine ⟨min y (x - 1 - f 0), min_le_left _ _, (hf1 _).trans_lt ?_⟩
        rw [← min_add_add_right, sub_add_cancel]
        exact min_lt_of_right_lt (sub_one_lt x)
      refine (hf2 _ (sub_pos.mpr h1)).trans ((hf _ _).trans ?_)
      rwa [add_le_add_iff_right, mul_le_mul_iff_of_pos_right h]
    replace hf (y) : y * f x ≤ 1 + f 0 + x := by
      specialize hf (-y)
      rwa [← neg_add', ← sub_le_iff_le_add, ← neg_add', neg_mul, neg_le_neg_iff] at hf
    replace hf1 := h.trans_le ((one_mul (f x)).symm.trans_le (hf 1))
    specialize hf ((1 + f 0 + x) * z)
    rwa [mul_assoc, mul_le_iff_le_one_right hf1] at hf
  ---- In reality, we only need `f(x) ≤ 1/3`
  specialize hf2 3 zero_le_three
  obtain ⟨C, hf3⟩ : ∃ C : R, ∀ y, 0 < y → y ≤ C := by
    refine ⟨-2 - 3 * f (-1), λ y hy ↦ ?_⟩
    have h : 3 * y = y * 3 := by
      rw [← two_add_one_eq_three, add_one_mul _ y, mul_add_one y, two_mul, mul_two]
    replace hf := mul_le_mul_of_nonneg_left (hf (f y - 1) y) zero_le_three
    rw [sub_sub_cancel_left, mul_add, ← mul_assoc, h, mul_assoc, mul_sub_one] at hf
    replace h : 3 * f (f y - 1) ≤ -1 := by
      apply (mul_le_mul_of_nonneg_left (hf1 _) zero_le_three).trans
      rw [← add_sub_right_comm, mul_sub_one, mul_add, sub_le_iff_le_add']
      apply (add_le_add (hf2 _) (hf2 _)).trans_eq
      rw [← two_add_one_eq_three, add_neg_cancel_right, one_add_one_eq_two]
    have h0 : 3 * f y - 3 ≤ -2 := by
      apply (sub_le_sub_right (hf2 _) 3).trans_eq
      rw [← two_add_one_eq_three, sub_add_cancel_right]
    replace hf := hf.trans (add_le_add (mul_le_mul_of_nonneg_left h hy.le) h0)
    rwa [mul_neg_one y, le_neg_add_iff_add_le, ← le_sub_iff_add_le] at hf
  obtain ⟨y, hy, hy0⟩ : ∃ y, 0 < y ∧ C < y :=
    ⟨max 0 C + 1, lt_add_of_le_of_pos (le_max_left 0 C) one_pos,
      lt_add_of_le_of_pos (le_max_right 0 C) one_pos⟩
  exact hy0.not_ge (hf3 y hy)
