/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring

/-!
# IMO 2008 A2 (P2)

1. Let $F$ be an ordered field, and consider $x, y, z ∈ F \setminus \{1\}$ with $xyz = 1$.
Prove that $$ \frac{x^2}{(x - 1)^2} + \frac{y^2}{(y - 1)^2} + \frac{z^2}{(z - 1)^2} ≥ 1. $$

2. Show that there exists infinitely many triplets $(x, y, z) ∈ (ℚ \setminus \{1\})^3$
  with $xyz = 1$ such that the above inequality becomes equality.
-/

namespace IMOSL
namespace IMO2008A2

/-! ### Part 1 -/

theorem ring_id1 [CommRing R] {a b c : R} (h : a * b * c = (a - 1) * (b - 1) * (c - 1)) :
    a ^ 2 + b ^ 2 + c ^ 2 - 1 = (a + b + c - 1) ^ 2 := calc
  _ = (a + b + c - 1) ^ 2 - 2 * (a * b * c - (a - 1) * (b - 1) * (c - 1)) := by ring
  _ = _ := by rw [sub_eq_zero_of_eq h, mul_zero, sub_zero]

/-- `x/(x - 1) - 1 = 1/(x - 1)` if `x ≠ 1`. -/
theorem field_eq1 [Field F] {x : F} (h : x ≠ 1) : x / (x - 1) - 1 = 1 / (x - 1) := by
  rw [div_sub_one (sub_ne_zero_of_ne h), sub_sub_cancel]

/-- If `xyz = 1` and `a = x/(x - 1)`, `b = y/(y - 1)`, `c = z/(z - 1)`,
  then `abc = (a - 1)(b - 1)(c - 1)`. -/
theorem field_eq2 [Field F]
    {x y z : F} (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) (h : x * y * z = 1) :
    x / (x - 1) * (y / (y - 1)) * (z / (z - 1))
      = (x / (x - 1) - 1) * (y / (y - 1) - 1) * (z / (z - 1) - 1) := by
  rw [field_eq1 hx, field_eq1 hy, field_eq1 hz, div_mul_div_comm,
    div_mul_div_comm, h, ← one_div_mul_one_div, ← one_div_mul_one_div]

/-- The main inequality -/
theorem ring_ineq1 [CommRing R] [LinearOrder R] [IsOrderedRing R]
    {a b c : R} (h : a * b * c = (a - 1) * (b - 1) * (c - 1)) :
    1 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [← sub_nonneg, ring_id1 h]; exact sq_nonneg _

/-- Final solution, part 1 -/
theorem final_solution_part1 [Field F] [LinearOrder F] [IsOrderedRing F]
    {x y z : F} (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) (h : x * y * z = 1) :
    1 ≤ (x / (x - 1)) ^ 2 + (y / (y - 1)) ^ 2 + (z / (z - 1)) ^ 2 :=
  ring_ineq1 (field_eq2 hx hy hz h)





/-! ### Part 2 -/

/-! ##### General lemmas -/

theorem ring_id2 [CommRing R] [NoZeroDivisors R] {a b c : R}
    (h : a * b * c = (a - 1) * (b - 1) * (c - 1)) (h0 : a + b + c = 1) :
    a ^ 2 + b ^ 2 + c ^ 2 = 1 := by
  rw [← sub_eq_zero, ring_id1 h, h0, sub_self, sq_eq_zero_iff]

theorem field_eq3 [Field F] {t : F} (h : t ≠ 0) (h0 : t + 1 ≠ 0) :
    -(t + 1) / t ^ 2 * (t / (t + 1) ^ 2) * -(t * (t + 1)) = 1 := by
  rw [neg_div, neg_mul, neg_mul_neg, div_mul_div_comm,
    ← mul_pow, mul_comm (t + 1), ← mul_div_right_comm, ← sq]
  exact div_self (pow_ne_zero 2 (mul_ne_zero h h0))

theorem field_eq4 [Field F] (a) {b : F} (h : b ≠ 0) :
    a / b / (a / b - 1) = a / (a - b) := by
  rw [div_div, mul_sub_one, mul_div_cancel₀ a h]

theorem field_eq5 [Field F] {t : F} (h : t ≠ 0) (h0 : t + 1 ≠ 0) (h1 : t * (t + 1) + 1 ≠ 0) :
    let x := -(t + 1) / t ^ 2
    let y := t / (t + 1) ^ 2
    let z := -(t * (t + 1))
    x / (x - 1) + y / (y - 1) + z / (z - 1) = 1 := by
  dsimp only; rw [field_eq4 _ (pow_ne_zero 2 h), field_eq4 _ (pow_ne_zero 2 h0)]
  have h2 : -(t + 1) - t ^ 2 = -(t * (t + 1) + 1) := by ring
  have h3 : t - (t + 1) ^ 2 = -(t * (t + 1) + 1) := by ring
  rw [h2, neg_div_neg_eq, h3, div_neg, ← sub_eq_add_neg, ← neg_add',
    neg_div_neg_eq, ← sub_div, ← add_div, add_sub_cancel_left, add_comm]
  exact div_self h1

section

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F] {t : F} (h : 0 < t)
include h

theorem field_ineq1 : -(t + 1) / t ^ 2 ≠ 1 :=
  div_ne_one_of_ne ((neg_lt_zero.mpr (add_pos h one_pos)).trans (pow_pos h 2)).ne

theorem field_ineq2 : t / (t + 1) ^ 2 ≠ 1 := by
  refine div_ne_one_of_ne ((lt_add_of_pos_left t h).trans ?_).ne
  rw [add_sq', mul_one, two_mul, one_pow, lt_add_iff_pos_left]
  exact add_pos (pow_pos h 2) one_pos

theorem field_ineq3 : -(t * (t + 1)) ≠ 1 :=
  ((neg_lt_zero.mpr (mul_pos h (add_pos h one_pos))).trans one_pos).ne

theorem field_eq6 :
    let x := -(t + 1) / t ^ 2
    let y := t / (t + 1) ^ 2
    let z := -(t * (t + 1))
    (x / (x - 1)) ^ 2 + (y / (y - 1)) ^ 2 + (z / (z - 1)) ^ 2 = 1 := by
  have h' : t ≠ 0 := h.ne.symm
  have h0 : 0 < t + 1 := add_pos h one_pos
  have h0' : t + 1 ≠ 0 := h0.ne.symm
  exact ring_id2
    (field_eq2 (field_ineq1 h) (field_ineq2 h) (field_ineq3 h) (field_eq3 h' h0'))
    (field_eq5 h' h0' (add_pos (mul_pos h h0) one_pos).ne.symm)

end



/-! ##### Restriction to ℚ -/

structure good (p : Fin 3 → ℚ) : Prop where
  p_ne_one : ∀ i, p i ≠ 1
  p_mul_eq_one : p 0 * p 1 * p 2 = 1
  spec : (p 0 / (p 0 - 1)) ^ 2 + (p 1 / (p 1 - 1)) ^ 2 + (p 2 / (p 2 - 1)) ^ 2 = 1





/-! ##### Construction -/

def ratMapSol (k : ℕ) : Fin 3 → ℚ
  | 0 => -(k.succ + 1) / k.succ ^ 2
  | 1 => k.succ / (k.succ + 1) ^ 2
  | 2 => -(k.succ * (k.succ + 1))

theorem ratMapSol_prod2_strictAnti : StrictAnti (λ k ↦ ratMapSol k 2) := λ k m h ↦ by
  unfold ratMapSol; simp only
  rw [neg_lt_neg_iff, ← Nat.cast_succ, ← Nat.cast_succ,
    ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_lt]
  replace h : k.succ < m.succ := Nat.succ_lt_succ h
  exact Nat.mul_lt_mul'' h ( Nat.succ_lt_succ h)

theorem ratMapSol_inj : ratMapSol.Injective :=
  λ _ _ h ↦ (ratMapSol_prod2_strictAnti.injective (congrFun h 2))

theorem ratMapSol_good (k) : good (ratMapSol k) :=
  have h : 0 < (k.succ : ℚ) := Nat.cast_pos.mpr k.succ_pos
  { p_ne_one := λ i ↦ match i with
      | 0 => field_ineq1 h
      | 1 => field_ineq2 h
      | 2 => field_ineq3 h
    p_mul_eq_one := field_eq3 h.ne.symm (add_pos h one_pos).ne.symm
    spec := field_eq6 h }

/-- Final solution, part 2 -/
theorem final_solution_part2 : {p : Fin 3 → ℚ | good p}.Infinite :=
  Set.infinite_of_injective_forall_mem ratMapSol_inj ratMapSol_good
