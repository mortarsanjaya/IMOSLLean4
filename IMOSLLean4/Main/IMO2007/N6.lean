/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Ring.Int

/-!
# IMO 2007 N6 (P5)

Fix $a > 1$, and let $x$ and $y$ be positive integers such that $axy - 1 ∣ (ax^2 - 1)^2$.
Prove that $x = y$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2007SL.pdf).
However, instead of inducting on $2x + y$, we induct on $x$.
-/

namespace IMOSL
namespace IMO2007N6

/-- A pair `(x, y)` is called a *bad pair* if `axy - 1 ∣ (ax^2 - 1)^2`. -/
abbrev bad_pair (a x y : ℤ) := a * x * y - 1 ∣ (a * x ^ 2 - 1) ^ 2

/-- Property (ii): if `(x, y)` is a bad pair, then so is `(y, x)`. -/
theorem bad_pair.symm (h : bad_pair a x y) : bad_pair a y x := by
  ---- First unfold everything in terms of modular arithmetic.
  rw [bad_pair, ← Int.modEq_zero_iff_dvd, Int.mul_right_comm] at h
  rw [bad_pair, ← Int.modEq_zero_iff_dvd]
  ---- Now do the computation.
  calc (a * y ^ 2 - 1) ^ 2
  _ ≡ (a * y ^ 2 - (a * y * x) ^ 2) ^ 2 [ZMOD a * y * x - 1] :=
    (((Int.modEq_sub _ _).pow 2).symm.sub_left _).pow 2
  _ ≡ (a * y ^ 2) ^ 2 * (a * x ^ 2 - 1) ^ 2 [ZMOD a * y * x - 1] := by
    rw [← Int.neg_sub 1 (a * x ^ 2), neg_sq, ← mul_pow, mul_one_sub,
      mul_mul_mul_comm, ← sq, ← mul_pow, ← mul_pow, mul_assoc]
  _ ≡ (a * y ^ 2) ^ 2 * 0 [ZMOD a * y * x - 1] := h.mul_left _
  _ ≡ 0 [ZMOD a * y * x - 1] := by rw [Int.mul_zero]

/-- A more general descent: if `N > 1`, `0 < x < y`, and `Ny - 1 ∣ (Nx - 1)^2`,
  then `(Ny - 1)(Nz - 1) = (Nx - 1)^2` for some positive integer `z < x`. -/
theorem general_descent {N x y : ℤ}
    (hN : N > 1) (hx : x > 0) (hxy : x < y) (h : N * y - 1 ∣ (N * x - 1) ^ 2) :
    ∃ z > 0, z < x ∧ (N * y - 1) * (N * z - 1) = (N * x - 1) ^ 2 := by
  ---- First write `(Nx - 1)^2 = (Ny - 1) t`.
  rcases h with ⟨t, h⟩
  ---- Working mod `N`, we get `t = Nz - 1` for some integer `z`.
  obtain ⟨z, rfl⟩ : ∃ z, t = N * z - 1 := by
    -- Applying mod `N` directly to `(Nx - 1)^2 = (Ny - 1) t` gives `1 ≡ -t (mod N)`.
    replace h : 1 ≡ -t [ZMOD N] := calc
      (0 - 1) ^ 2 ≡ (N * x - 1) ^ 2 [ZMOD N] :=
        ((Int.dvd_mul_right N x).zero_modEq_int.sub_right 1).pow 2
      _ ≡ (N * y - 1) * t [ZMOD N] := by rw [h]
      _ ≡ (0 - 1) * t [ZMOD N] :=
        ((Int.dvd_mul_right N y).modEq_zero_int.sub_right 1).mul_right t
      _ ≡ -t [ZMOD N] := by rw [Int.zero_sub, Int.neg_one_mul]
    -- Thus `N ∣ t + 1` and we are done.
    rw [Int.modEq_iff_dvd, ← neg_add', Int.dvd_neg] at h
    rcases h with ⟨z, h⟩
    exact ⟨z, eq_sub_iff_add_eq.mpr h⟩
  ---- An auxiliary lemma: if `c > 0` then `Nc - 1 > 0` (and so `Ny - 1 > 0`).
  have hN0 {c} (hc : 0 < c) : N * c - 1 > 0 :=
    sub_pos_of_lt (one_lt_mul_of_lt_of_le hN (by exact hc))
  have hN0y : N * y - 1 > 0 := hN0 (hx.trans hxy)
  ---- From now on, we only need `N > 0` as opposed to `N > 1`.
  replace hN : N > 0 := Int.one_pos.trans hN
  ---- Now it remains to show that `0 < z < x`; both by contradiction.
  refine ⟨z, ?_, ?_, h.symm⟩
  ---- First, show that `z > 0`.
  · refine lt_of_not_ge λ hz ↦ h.not_gt ?_
    -- If `z ≤ 0`, then `Nz - 1 < 0`.
    replace hz : N * z - 1 < 0 := calc
      N * z - 1 < N * z := sub_one_lt _
      _ ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hN.le hz
    -- Thus `(Ny - 1)(Nz - 1) < 0 ≤ (Nx - 1)^2`; contradiction.
    calc (N * y - 1) * (N * z - 1)
      _ < 0 := mul_neg_of_pos_of_neg hN0y hz
      _ ≤ (N * x - 1) ^ 2 := sq_nonneg _
  ---- Second, show that `z < x`.
  · -- Since `y > x`, we have `Ny - 1 > Nx - 1`.
    replace hxy : N * x - 1 < N * y - 1 :=
      Int.sub_lt_sub_right (Int.mul_lt_mul_of_pos_left hxy hN) 1
    -- If `z ≥ x`, then `Nz - 1 ≥ Nx - 1`.
    refine lt_of_not_ge λ hxz ↦ h.not_lt ?_
    replace hxz : N * x - 1 ≤ N * z - 1 :=
      Int.sub_le_sub_right (Int.mul_le_mul_of_nonneg_left hxz hN.le) 1
    -- But then `(Ny - 1)(Nz - 1) > (Nx - 1)^2`; contradiction.
    calc (N * x - 1) ^ 2
      _ = (N * x - 1) * (N * x - 1) := sq _
      _ < (N * y - 1) * (N * z - 1) := Int.mul_lt_mul hxy hxz (hN0 hx) hN0y.le

/-- Property (i): If `(x, y)` is a bad pair with `0 < x < y`,
  then `(z, x)` is a bad pair for some integer `z` with `0 < z < x`. -/
theorem bad_pair.descent (ha : a > 1) (hx : x > 0) (hxy : x < y) (h : bad_pair a x y) :
    ∃ z > 0, z < x ∧ bad_pair a x z := by
  ---- This essentially follows from the `general_descent` step.
  rw [bad_pair, sq x, ← Int.mul_assoc] at h
  obtain ⟨z, hz, hzx, h0⟩ : ∃ z > 0, z < x ∧ _ :=
    general_descent (one_lt_mul_of_lt_of_le ha hx) hx hxy h
  refine ⟨z, hz, hzx, a * x * y - 1, ?_⟩
  rw [sq x, ← Int.mul_assoc, ← h0, Int.mul_comm]

/-- Final solution -/
theorem final_solution (ha : 1 < a) (hx : x > 0) (hy : y > 0) (h : bad_pair a x y) :
    x = y := by
  ---- Strong induction on `x`.
  induction x using Int.strongRec (m := 1) generalizing y with
  | lt x hx0 => exact absurd hx hx0.not_ge
  | ge x hx0 x_ih => ?_
  ---- Split into 3 cases: `x < y`, `x = y`, and `y < x`.
  obtain h0 | h0 | h0 : x < y ∨ x = y ∨ y < x := Int.lt_trichotomy x y
  ---- Case 1: `x < y`; then `(z, x)` is a bad pair for some `z < x`, contradiction.
  · obtain ⟨z, hz, hzx, h1⟩ := h.descent ha hx h0
    exact absurd (x_ih z hzx hz hx h1.symm) hzx.ne
  ---- Case 2: `x = y`; this is the goal.
  · exact h0
  ---- Case 3: `x > y`; then `(y, x)` is a bad pair and `y < x`, contradiction.
  · exact (x_ih y h0 hy hx h.symm).symm
