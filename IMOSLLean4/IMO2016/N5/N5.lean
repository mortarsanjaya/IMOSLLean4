/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-!
# IMO 2016 N5

Fix some $k, a ∈ ℤ$ with $k ≥ 0$ and $a > 0$.
A pair $(x, y) ∈ ℤ^2$ is called *nice* if $(k + 1) y^2 - k x^2 = a$.
Prove that the following two statements are equivalent:
* There exists a nice pair $(x, y)$ with $x ≥ 0$ and $x^2 > a$;
* There exists a nice pair $(x, y)$ with $x ≥ 0$ and $x^2 ≤ a$.
-/

namespace IMOSL
namespace IMO2016N5

def nice (k a x y : ℤ) := (k + 1) * y ^ 2 - k * x ^ 2 = a



namespace nice

section

variable (h : nice k a x y)
include h

theorem neg_left : nice k a (-x) y := by
  rwa [nice, neg_sq]

theorem neg_right : nice k a x (-y) := by
  rwa [nice, neg_sq]

theorem neg_neg : nice k a (-x) (-y) :=
  h.neg_left.neg_right

theorem abs_left : nice k a |x| y := by
  rwa [nice, sq_abs]

theorem abs_right : nice k a x |y| := by
  rwa [nice, sq_abs]

theorem abs_abs : nice k a |x| |y| :=
  h.abs_left.abs_right

theorem linear_transform :
    nice k a ((2 * k + 1) * x + 2 * (k + 1) * y) (2 * k * x + (2 * k + 1) * y) := calc
  _ = (k + 1) * y ^ 2 - k * x ^ 2 := by ring
  _ = a := h

theorem k_mirror : nice (-(k + 1)) a y x := by
  rwa [nice, neg_mul, sub_neg_eq_add, add_comm,
    neg_add', sub_add_cancel, neg_mul, ← sub_eq_add_neg]

end


theorem y_ne_zero (hk : 0 ≤ k) (ha : 0 < a) (h : nice k a x y) : y ≠ 0 := λ h1 ↦ by
  rw [h1, nice, zero_pow (Nat.succ_ne_zero 1), mul_zero, zero_sub] at h
  exact h.not_lt ((neg_nonpos.mpr (mul_nonneg hk (sq_nonneg x))).trans_lt ha)

end nice





variable {k a : ℤ} (hk : 0 ≤ k) (ha : 0 < a)
include hk ha

/-- Generate a new nice pair `(x', y')` with `x'` arbitrarily big from any nice pair -/
theorem exists_x_ge_bound_nat (h : ∃ x y, nice k a x y) :
    ∀ N : ℕ, ∃ x y : ℤ, 0 ≤ x ∧ N ≤ x ^ 2 ∧ nice k a x y := by
  ---- Set up induction on `N`
  refine Nat.rec ?_ (λ N h0 ↦ ?_)
  · rcases h with ⟨x, y, h⟩; exact ⟨|x|, |y|, abs_nonneg x, sq_nonneg _, h.abs_abs⟩
  clear h; rcases h0 with ⟨x, y, hx, hx0, h⟩
  ---- Now focus on the induction step
  have X : (0 : ℤ) ≤ 1 := Int.zero_le_ofNat 1
  have X0 : (0 : ℤ) ≤ 2 := Int.zero_le_ofNat 2
  have X1 : (0 : ℤ) ≤ 2 * k := Int.mul_nonneg X0 hk
  have X2 : (0 : ℤ) < 2 * (k + 1) := Int.mul_pos two_pos (Int.lt_add_one_of_le hk)
  refine ⟨(2 * k + 1) * x + 2 * (k + 1) * |y|, 2 * k * x + (2 * k + 1) * |y|,
    add_nonneg (mul_nonneg (add_nonneg X1 X) hx) (mul_nonneg X2.le (abs_nonneg y)),
    ?_, h.abs_right.linear_transform⟩
  ---- `0 ≤ x'` and `nice k a x' y'` are immediately resolved; left with `N + 1 ≤ x' ^ 2`
  rw [Nat.cast_succ, Int.add_one_le_iff]
  refine hx0.trans_lt (pow_lt_pow_left₀ ?_ hx (Nat.succ_ne_zero 1))
  rw [add_one_mul (2 * k), add_right_comm, lt_add_iff_pos_left]
  exact add_pos_of_nonneg_of_pos (mul_nonneg X1 hx)
    (mul_pos X2 (abs_pos.mpr (h.y_ne_zero hk ha)))

/-- Generate a new nice pair `(x', y')` with `x' ≤ √a` from any nice pair -/
theorem exists_x_sq_le_a (h : ∃ x y, nice k a x y) :
    ∃ x y : ℤ, 0 ≤ x ∧ x ^ 2 ≤ a ∧ nice k a x y := by
  ---- Reduce to a decreasing induction statement
  let P (N : ℕ) : Prop := ∃ x y : ℤ, 0 ≤ x ∧ x ^ 2 ≤ N ∧ nice k a x y
  suffices P a.natAbs by
    dsimp only [P] at this; rwa [Int.natCast_natAbs, abs_of_nonneg ha.le] at this
  revert h; suffices ∀ N, a.natAbs ≤ N → P (N + 1) → P N by
    rintro ⟨x, y, h⟩
    obtain h0 | h0 : x ^ 2 ≤ a.natAbs ∨ a.natAbs ≤ x ^ 2 := le_total _ _
    · exact ⟨|x|, y, abs_nonneg x, (sq_abs _).trans_le h0, h.abs_left⟩
    -- Focus on the case `a < x^2`
    replace h0 : a.natAbs ≤ x.natAbs ^ 2 := by
      rwa [← sq_abs, ← Int.natCast_natAbs, ← Nat.cast_pow, Nat.cast_le] at h0
    refine Nat.decreasingInduction' (λ k _ ↦ this k) h0 ⟨|x|, y, abs_nonneg _, ?_, h.abs_left⟩
    rw [Nat.cast_pow, Int.natCast_natAbs]
  ---- Resolve the decreasing induction step; immediately solve the case `x^2 ≤ N`
  rintro N hN ⟨x, y, hx, hx0, h0⟩
  rw [Nat.cast_succ, Int.le_add_one_iff] at hx0
  rcases hx0 with hx0 | hx0
  · exact ⟨x, y, hx, hx0, h0⟩
  ---- Focus on the case `x^2 = N + 1`
  refine ⟨_, _, abs_nonneg _, ?_, h0.abs_abs.neg_right.linear_transform.abs_left⟩
  rw [← Int.lt_add_one_iff, ← hx0, sq_lt_sq, abs_abs, mul_neg, abs_lt]
  have hk0 : 0 < k + 1 := Int.lt_add_one_of_le hk
  have h1 : |y| < |x| := by
    rw [← sq_lt_sq, ← mul_lt_mul_iff_of_pos_left hk0, (eq_add_of_sub_eq' h0), add_one_mul k]
    refine add_lt_add_left (lt_of_abs_lt ?_) _
    rwa [hx0, Int.lt_add_one_iff, ← Int.natCast_natAbs, Nat.cast_le]
  refine ⟨?_, ?_⟩
  ---- Goal 1: `-|x| < (2k + 1) |x| - 2(k + 1) |y|`
  · have h2 : 0 < 2 * (k + 1) := mul_pos two_pos hk0
    rwa [lt_add_neg_iff_add_lt, neg_add_lt_iff_lt_add', ← add_one_mul,
      add_assoc, one_add_one_eq_two, ← mul_add_one 2 k, mul_lt_mul_iff_of_pos_left h2]
  ---- Goal 2: `(2k + 1) |x| - 2(k + 1) |y| < |x|`
  · rw [add_neg_lt_iff_lt_add, add_one_mul _ |x|, add_comm]
    refine add_lt_add_left (lt_of_not_ge λ h2 ↦ ?_) _
    rw [mul_assoc, mul_assoc, mul_le_mul_iff_of_pos_left two_pos] at h2
    apply (mul_le_mul h2 h1.le (abs_nonneg y) (mul_nonneg hk (abs_nonneg x))).not_gt
    rwa [mul_assoc, mul_assoc, ← sq, sq_abs, ← sq, sq_abs, ← sub_pos, h0]





/-! ### Summary -/

/-- Final solution -/
theorem final_solution :
    (∃ x y, 0 ≤ x ∧ a < x ^ 2 ∧ nice k a x y)
      ↔ (∃ x y, 0 ≤ x ∧ x ^ 2 ≤ a ∧ nice k a x y) := by
  refine ⟨λ ⟨x, y, _, _, h⟩ ↦ exists_x_sq_le_a hk ha ⟨x, y, h⟩, λ ⟨x, y, _, _, h⟩ ↦ ?_⟩
  obtain ⟨x, y, h0, h1, h2⟩ := exists_x_ge_bound_nat hk ha ⟨x, y, h⟩ (a.natAbs + 1)
  refine ⟨x, y, h0, ?_, h2⟩
  rw [Nat.cast_succ, Int.add_one_le_iff, Int.natCast_natAbs] at h1
  exact lt_of_abs_lt h1
