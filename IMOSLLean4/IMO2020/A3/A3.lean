/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# IMO 2020 A3

Find the smallest possible value of $a/b + b/c + c/d + d/a$ across
  all $a, b, c, d ∈ ℝ$ such that $(a + c)(b + d) = ac + bd$.
-/

namespace IMOSL
namespace IMO2020A3

def good [Semiring R] (x : Fin 4 → R) :=
  (x 0 + x 2) * (x 1 + x 3) = x 0 * x 2 + x 1 * x 3

def targetVal [Semifield F] (x : Fin 4 → F) :=
  x 0 / x 1 + x 1 / x 2 + x 2 / x 3 + x 3 / x 0



theorem ring_ineq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
    (a b : R) : 2 ^ 2 * (a * b) ≤ (a + b) ^ 2 := by
  rw [sq, two_mul, add_mul, ← mul_assoc, add_sq', add_le_add_iff_right]
  exact two_mul_le_add_sq a b

theorem field_ineq [Semifield F] [LinearOrder F] [IsStrictOrderedRing F] [ExistsAddOfLE F]
    (a b c d : F) : 2 ^ 2 * (a * c / (b * d)) ≤ (a / b + c / d) ^ 2 :=
  div_mul_div_comm a b c d ▸ ring_ineq _ _

theorem good_ineq1 [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
    {x : Fin 4 → R} (h : ∀ i, 0 < x i) (h0 : good x) :
    2 ^ 4 * (x 0 * x 2 * (x 1 * x 3)) ≤ (x 0 * x 2 + x 1 * x 3) ^ 2 := by
  rw [pow_add 2 2 2, mul_mul_mul_comm]
  apply (mul_le_mul (ring_ineq _ _) (ring_ineq _ _)
    (mul_nonneg (sq_nonneg 2) (mul_pos (h 1) (h 3)).le) (sq_nonneg _)).trans_eq
  rw [← mul_pow, h0]

theorem good_ineq2 [Semifield F] [LinearOrder F] [IsStrictOrderedRing F] [ExistsAddOfLE F]
    {x : Fin 4 → F} (h : ∀ i, 0 < x i) (h0 : good x) :
    2 ^ 4 ≤ x 0 * x 2 / (x 1 * x 3) + x 1 * x 3 / (x 0 * x 2) + 2 := by
  have h1 : 0 < x 0 * x 2 := mul_pos (h 0) (h 2)
  have h2 : 0 < x 1 * x 3 := mul_pos (h 1) (h 3)
  have h3 : 0 < (x 0 * x 2) * (x 1 * x 3) := mul_pos h1 h2
  rw [div_add_div _ _ h2.ne.symm h1.ne.symm, ← sq, ← sq, mul_comm (x 1 * x 3),
    div_add' _ _ _ h3.ne.symm, ← mul_assoc, ← add_sq', le_div_iff₀ h3]
  exact good_ineq1 h h0

theorem good_ineq3 [Semifield F] [LinearOrder F] [IsStrictOrderedRing F] [ExistsAddOfLE F]
    {x : Fin 4 → F} (h : ∀ i, 0 < x i) (h0 : good x) : 8 ≤ targetVal x := by
  ---- Reduce to `(x_0/x_1 + x_1/x_2 + x_2/x_3 + x_3/x_4)^2 ≥ 64`
  have X : (8 : F) = 2 ^ 3 := by rw [← Nat.cast_two, ← Nat.cast_pow]; rfl
  rw [targetVal, add_assoc, add_add_add_comm, X]
  replace X (i) : 0 < x i / x (i + 1) + x (i + 2) / x (i + 3) :=
    add_pos (div_pos (h i) (h (i + 1))) (div_pos (h (i + 2)) (h (i + 3)))
  apply le_of_pow_le_pow_left₀ (Nat.succ_ne_zero 1) (add_pos (X 0) (X 1)).le
  ---- Reduce to `LHS ≥ 4(x_0 x_2/x_1 x_3 + x_1 x_3/x_0 x_2 + 2)`
  rw [← pow_mul, pow_add 2 2 4]
  apply (mul_le_mul_of_nonneg_left (good_ineq2 h h0) (sq_nonneg 2)).trans
  ---- Reduce to `(x_0 x_2/x_1 x_3)(x_1 x_3/x_0 x_2) ≥ 4`
  have h1 := field_ineq (x 0) (x 1) (x 2) (x 3)
  have h2 := field_ineq (x 1) (x 2) (x 3) (x 0)
  rw [mul_comm (x 2) (x 0)] at h2
  rw [add_sq', mul_add, mul_add, mul_comm _ 2, mul_assoc 2]
  refine add_le_add (add_le_add h1 h2) (mul_le_mul_of_nonneg_left ?_ zero_le_two)
  ---- Prove `(x_0/x_1 + x_2/x_3)(x_1/x_2 + x_3/x_0) ≥ 4`
  refine le_of_pow_le_pow_left₀ (Nat.succ_ne_zero 1) (mul_pos (X 0) (X 1)).le ?_
  have h3 : 0 < x 1 * x 3 / (x 0 * x 2) :=
    div_pos (mul_pos (h 1) (h 3)) (mul_pos (h 0) (h 2))
  rw [sq, mul_pow]
  apply (mul_le_mul h1 h2 (mul_nonneg (sq_nonneg 2) h3.le) (sq_nonneg _)).trans_eq'
  rw [mul_mul_mul_comm, ← inv_div, inv_mul_cancel₀ h3.ne.symm, mul_one]



/-! ### Solution for rings with `√3` -/

class HasSqrt3 (R) [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] where
  sqrt3 : R
  sqrt3_nonneg : 0 ≤ sqrt3
  sqrt3_sq : sqrt3 ^ 2 = 3

notation : max "√3" => HasSqrt3.sqrt3

open HasSqrt3

section

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [HasSqrt3 R]

lemma two_add_sqrt3_pos : 0 < 2 + (√3 : R) :=
  add_pos_of_pos_of_nonneg two_pos sqrt3_nonneg

lemma two_add_sqrt3_sq_add_one : (2 + √3 : R) ^ 2 + 1 = 4 * (2 + √3) := by
  have X : (2 : R) * 2 = 4 := by rw [← Nat.cast_two, ← Nat.cast_mul]; rfl
  rw [add_sq', add_right_comm, sqrt3_sq, add_assoc _ 3,
    three_add_one_eq_four, sq, X, ← mul_two, ← mul_add]

lemma sqrt3_seq_pos (i) : 0 < ![2 + (√3 : R), 1, 2 + √3, 1] i :=
  have X : 0 < 2 + (√3 : R) := two_add_sqrt3_pos
  match i with | 0 => X | 1 => one_pos | 2 => X | 3 => one_pos

lemma sqrt3_seq_good : good (R := R) ![2 + √3, 1, 2 + √3, 1] := by
  show ((2 + √3) + (2 + √3)) * (1 + 1) = (2 + √3) * (2 + √3) + 1 * 1
  have X : (2 : R) * 2 = 4 := by rw [← Nat.cast_two, ← Nat.cast_mul]; rfl
  rw [one_add_one_eq_two, ← two_mul, mul_right_comm,
    X, ← sq, one_mul, two_add_sqrt3_sq_add_one]

end



variable [Semifield F] [LinearOrder F] [IsStrictOrderedRing F] [ExistsAddOfLE F] [HasSqrt3 F]

lemma sqrt3_seq_targetVal : targetVal (F := F) ![2 + √3, 1, 2 + √3, 1] = 8 := by
  show (2 + √3 : F) / 1 + 1 / (2 + √3) + (2 + √3) / 1 + 1 / (2 + √3) = 8
  suffices (2 + √3 : F) + (2 + √3)⁻¹ = 4 by
    rw [div_one, one_div, add_assoc, this, ← Nat.cast_ofNat, ← Nat.cast_add]; rfl
  have X : (2 + √3 : F) ≠ 0 := two_add_sqrt3_pos.ne.symm
  apply mul_right_cancel₀ X
  rw [add_mul, ← sq, inv_mul_cancel₀ X, two_add_sqrt3_sq_add_one]

/-- Final solution -/
theorem final_solution :
    IsLeast {M | ∃ x : Fin 4 → F, (∀ i, 0 < x i) ∧ good x ∧ targetVal x = M} 8 :=
  ⟨⟨_, sqrt3_seq_pos, sqrt3_seq_good, sqrt3_seq_targetVal⟩,
    λ _ ⟨_, h, h0, h1⟩ ↦ (good_ineq3 h h0).trans_eq h1⟩
