/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Real.Sqrt

/-!
# IMO 2009 A4

Let $a, b, c ∈ ℝ⁺$ such that $1/a + 1/b + 1/c ≤ 3$.
Prove that
$$ \sqrt{\frac{a^2 + b^2}{a + b}} + \sqrt{\frac{b^2 + c^2}{b + c}}
    + \sqrt{\frac{c^2 + a^2}{c + a}} + 3
  ≤ \sqrt{2} (\sqrt{a + b} + \sqrt{b + c} + \sqrt{c + a}). $$

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
More generally, we prove that for any positive real numbers $x_1, …, x_n, y_1, …, y_n$,
$$ \sum_{i = 1}^n \sqrt{\frac{x_i^2 + y_i^2}{x_i + y_i}}
    + n \sqrt{\frac{2n}{\sum_{i = 1}^n (x_i^{-1} + y_i^{-1})}}
  ≤ \sqrt{2} \sum_{i = 1}^n \sqrt{x_i + y_i}. $$
This general inequality is proved in `ineq3`.
-/

namespace IMOSL
namespace IMO2009A4

open NNReal Finset

/-- The inequality `√a + √b ≤ √(2(a + b))` for nonnegative real numbers. -/
theorem sqrt_add_sqrt_le_sqrt_two_mul_add (a b : ℝ≥0) :
    sqrt a + sqrt b ≤ sqrt (2 * (a + b)) :=
  le_sqrt_iff_sq_le.mpr (add_sq_le.trans_eq (by simp only [sq_sqrt]))

/-- The inequality `√((a^2 + b^2)/(a + b)) + √(2/(a⁻¹ + b⁻¹)) ≤ √(2(a + b))`. -/
theorem ineq1 {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0) :
    sqrt ((a ^ 2 + b ^ 2) / (a + b)) + sqrt 2 * sqrt (a⁻¹ + b⁻¹)⁻¹ ≤ sqrt (2 * (a + b)) :=
  calc sqrt ((a ^ 2 + b ^ 2) / (a + b)) + sqrt 2 * sqrt (a⁻¹ + b⁻¹)⁻¹
  _ = sqrt ((a ^ 2 + b ^ 2) / (a + b)) + sqrt (2 / (a⁻¹ + b⁻¹)) := by
    rw [← sqrt_mul, ← div_eq_mul_inv]
  _ ≤ sqrt (2 * ((a ^ 2 + b ^ 2) / (a + b) + 2 / (a⁻¹ + b⁻¹))) :=
    sqrt_add_sqrt_le_sqrt_two_mul_add _ _
  _ = sqrt (2 * (a + b)) := by
    refine congrArg (λ x ↦ sqrt (2 * x)) ?_
    rw [inv_add_inv ha hb, ← div_mul, ← mul_div_right_comm, ← add_div,
      ← mul_assoc, ← add_sq', sq, mul_div_cancel_right₀ _ (add_ne_zero.mpr (Or.inl ha))]

/-- Hölder's inequality: if `z_i^3 ≤ x_i y_i` for all `i`,
  then of form `√(∑_i z_i)^3 ≤ (∑_i √x_i)^2 (∑_i y_i)`. -/
theorem Hölder_one_and_half
    (I : Finset ι) {x y z : ι → ℝ≥0} (h : ∀ i ∈ I, z i ^ 3 = x i * y i) :
    sqrt ((∑ i ∈ I, z i) ^ 3) ≤ (∑ i ∈ I, sqrt (x i)) * sqrt (∑ i ∈ I, y i) := by
  ---- If `∑_i z_i = 0` we are done.
  obtain hz | hz : ∑ i ∈ I, z i = 0 ∨ ∑ i ∈ I, z i > 0 := eq_zero_or_pos _
  · rw [hz, pow_succ, mul_zero, sqrt_zero]
    exact zero_le _
  ---- If `∑_i z_i > 0`, then multiply both sides by `√(∑_i z_i)`.
  refine le_of_mul_le_mul_of_pos_right ?_ (sqrt_pos.mpr hz)
  ---- Then apply double Cauchy-Schwarz afterwards.
  calc sqrt ((∑ i ∈ I, z i) ^ 3) * sqrt (∑ i ∈ I, z i)
    _ = (∑ i ∈ I, z i) ^ 2 := by
      rw [← sqrt_mul, ← pow_succ, pow_mul _ 2 2, sqrt_sq]
    _ ≤ (∑ i ∈ I, sqrt (x i)) * ∑ i ∈ I, sqrt (y i) * sqrt (z i) := by
      refine sum_sq_le_sum_mul_sum_of_sq_eq_mul _
        (λ _ _ ↦ zero_le _) (λ _ _ ↦ zero_le _) (λ i hi ↦ ?_)
      rw [← sqrt_mul, ← sqrt_mul, eq_comm, sqrt_eq_iff_eq_sq,
        ← pow_mul, pow_succ, h i hi, mul_assoc]
    _ ≤ (∑ i ∈ I, sqrt (x i)) * (sqrt (∑ i ∈ I, y i) * sqrt (∑ i ∈ I, z i)) :=
      mul_le_mul_right (sum_sqrt_mul_sqrt_le I y z) _
    _ = (∑ i ∈ I, sqrt (x i)) * sqrt (∑ i ∈ I, y i) * sqrt (∑ i ∈ I, z i) :=
      (mul_assoc _ _ _).symm

/-- The inequality `#I √(#I/∑_{i ∈ I} x_i) ≤ ∑_{i ∈ I} 1/√x_i`. -/
theorem ineq2 (I : Finset ι) {x : ι → ℝ≥0} (hx : ∀ i ∈ I, x i ≠ 0) :
    #I * sqrt (#I / ∑ i ∈ I, x i) ≤ ∑ i ∈ I, sqrt (x i)⁻¹ := by
  ---- First move the denominator to the right.
  rw [sqrt_div, ← mul_div_assoc]
  refine div_le_of_le_mul ?_
  ---- Now apply Hölder's inequality.
  calc (#I : ℝ≥0) * sqrt (#I)
    _ = sqrt ((∑ i ∈ I, 1) ^ 3) := by
      rw [sum_const, nsmul_one, pow_succ, sqrt_mul, sqrt_sq]
    _ ≤ (∑ i ∈ I, sqrt (x i)⁻¹) * sqrt (∑ i ∈ I, x i) :=
      Hölder_one_and_half I λ i hi ↦ by rw [one_pow, inv_mul_cancel₀ (hx i hi)]

/-- The general form of the inequality to be proved. -/
theorem ineq3 (I : Finset ι) {x y : ι → ℝ≥0}
    (hx : ∀ i ∈ I, x i ≠ 0) (hy : ∀ i ∈ I, y i ≠ 0) :
    ∑ i ∈ I, sqrt ((x i ^ 2 + y i ^ 2) / (x i + y i))
        + #I * sqrt (2 * #I / ∑ i ∈ I, ((x i)⁻¹ + (y i)⁻¹))
      ≤ sqrt 2 * ∑ i ∈ I, sqrt (x i + y i) :=
  calc ∑ i ∈ I, sqrt ((x i ^ 2 + y i ^ 2) / (x i + y i))
        + #I * sqrt (2 * #I / ∑ i ∈ I, ((x i)⁻¹ + (y i)⁻¹))
  _ = ∑ i ∈ I, sqrt ((x i ^ 2 + y i ^ 2) / (x i + y i))
      + sqrt 2 * (#I * sqrt (#I / ∑ i ∈ I, ((x i)⁻¹ + (y i)⁻¹))) := by
    rw [mul_left_comm, ← sqrt_mul, mul_div_assoc]
  _ ≤ ∑ i ∈ I, sqrt ((x i ^ 2 + y i ^ 2) / (x i + y i))
      + sqrt 2 * ∑ i ∈ I, sqrt ((x i)⁻¹ + (y i)⁻¹)⁻¹ :=
    add_le_add_right (a := _) <| mul_le_mul_right (a := _) <|
      ineq2 _ λ i hi ↦ add_ne_zero.mpr (Or.inl (inv_ne_zero (hx i hi)))
  _ = ∑ i ∈ I, (sqrt ((x i ^ 2 + y i ^ 2) / (x i + y i)) + sqrt 2 * sqrt ((x i)⁻¹ + (y i)⁻¹)⁻¹) := by
    rw [mul_sum, sum_add_distrib]
  _ ≤ ∑ i ∈ I, sqrt (2 * (x i + y i)) :=
    sum_le_sum λ i hi ↦ ineq1 (hx i hi) (hy i hi)
  _ = ∑ i ∈ I, sqrt 2 * sqrt (x i + y i) :=
    sum_congr rfl λ i _ ↦ sqrt_mul _ _
  _ = sqrt 2 * ∑ i ∈ I, sqrt (x i + y i) :=
    (mul_sum _ _ _).symm

/-- Specialiation of `ineq3` over `Fin n` as index with `y_i = x_{i + j}` for some `j`. -/
theorem ineq4 {x : Fin n → ℝ≥0} (hx : ∀ i, x i ≠ 0) (j : Fin n) :
    ∑ i, sqrt ((x i ^ 2 + x (i + j) ^ 2) / (x i + x (i + j))) + n * sqrt (n / ∑ i, (x i)⁻¹)
      ≤ sqrt 2 * ∑ i, sqrt (x i + x (i + j)) :=
  let I : Finset (Fin n) := univ
  calc ∑ i, sqrt ((x i ^ 2 + x (i + j) ^ 2) / (x i + x (i + j))) + n * sqrt (n / ∑ i, (x i)⁻¹)
  _ = ∑ i, sqrt ((x i ^ 2 + x (i + j) ^ 2) / (x i + x (i + j)))
      + #I * sqrt ((2 * #I) / ∑ i, ((x i)⁻¹ + (x (i + j))⁻¹)) := by
    cases n with
    | zero => simp_rw [I, univ_eq_empty, card_empty, sum_empty, div_zero]
    | succ n => ?_
    -- The case `n = 0` is separate since the proof below works only for `n > 0`.
    have h : ∑ i, (x (i + j))⁻¹ = ∑ i, (x i)⁻¹ :=
      Fintype.sum_equiv (Equiv.addRight j) _ _ (λ _ ↦ rfl)
    rw [add_right_inj, card_univ, Fintype.card_fin, sum_add_distrib,
      h, ← two_mul, mul_div_mul_left _ _ two_ne_zero]
  _ ≤ sqrt 2 * ∑ i, sqrt (x i + x (i + j)) :=
    ineq3 (x := x) (y := λ i ↦ x (i + j)) univ (λ i _ ↦ hx i) (λ i _ ↦ hx (i + j))

/-- Final solution -/
theorem final_solution {x : Fin 3 → ℝ≥0} (hx : ∀ i, x i > 0) (hx0 : ∑ i, (x i)⁻¹ ≤ 3) :
    ∑ i, sqrt ((x i ^ 2 + x (i + 1) ^ 2) / (x i + x (i + 1))) + 3
      ≤ sqrt 2 * ∑ i, sqrt (x i + x (i + 1)) :=
  calc ∑ i, sqrt ((x i ^ 2 + x (i + 1) ^ 2) / (x i + x (i + 1))) + 3
  _ ≤ ∑ i, sqrt ((x i ^ 2 + x (i + 1) ^ 2) / (x i + x (i + 1))) + 3 * sqrt (3 / ∑ i, (x i)⁻¹) :=
    have h : 0 < ∑ i, (x i)⁻¹ :=
      Fintype.sum_pos (lt_of_strongLT λ i ↦ inv_pos.mpr (hx i))
    add_le_add_right (a := _) <| le_mul_of_one_le_right zero_le_three <|
      one_le_sqrt.mpr ((one_le_div h).mpr hx0)
  _ ≤ sqrt 2 * ∑ i, sqrt (x i + x (i + 1)) := ineq4 (λ i ↦ (hx i).ne.symm) 1
