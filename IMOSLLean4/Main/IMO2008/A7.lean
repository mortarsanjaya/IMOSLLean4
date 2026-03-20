/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Field

/-!
# IMO 2008 A7

Let $F$ be a totally ordered field.
Let $x_0, x_1, x_2, x_3 ∈ F$ be positive elements, and denote
$$ L = \sum_{i = 0}^3 \frac{(x_i - x_{i + 1})(x_i - x_{i + 2})}{x_i + x_{i + 1} + x_{i + 2}}, $$
  where we set $x_{i + 4} = x_i$ for all $i ≥ 0$.
1. Prove that $L ≥ 0$.
2. Determine when $L = 0$ holds.

### Answer for part 2

We have $L = 0$ if and only if $x_0 = x_2$ and $x_1 = x_3$.

### Solution

Our beginning is similar to Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2008SL.pdf),
  but we prove the following sharper estimate while avoiding square roots.
Let $ε_1 = x_0 - x_2$, $ε_2 = x_1 - x_3$, and $S = x_0 + x_1 + x_2 + x_3$.
Then we prove the estimate
$$ L ≥ \frac{4(|ε_1| + |ε_2|)^2 - 9|ε_1||ε_2|}{6S}. $$
This solves both parts since $4 \cdot 4 = 16 > 9$.

First notice the following inequality for any $a, b, c, d > 0$:
\begin{align*}
  & \frac{(a - b)(a - c)}{a + b + c} + \frac{(c - d)(c - a)}{c + d + a} \\\\
  =\\;& \frac{(a - c)^2}{2(a + b + c)} + \frac{(a - c)^2}{2(c + d + a)}
    - \frac{3(a + c)(a - c)(b - d)}{2(a + c + b)(a + c + d)} \\\\
  \geq\\;& \frac{2(a - c)^2}{2(a + c) + (b + d)}
    - \frac{3(a + c) (a - c)(b - d)}{2(a + c + b)(a + c + d)},
\end{align*}
  where the last inequality follows by Cauchy-Schwarz inequality.
Now let $y = x_0 + x_2$ and $z = x_1 + x_3$.
Applying the above inequality and Cauchy-Schwarz inequality again, we get
\begin{align*}
  L &\geq \frac{2ε_1^2}{2y + z} + \frac{2ε_2^2}{2z + y} - \frac{3 ε_1 ε_2}{2}
      \left(\frac{y}{(y + x_1)(y + x_3)} - \frac{z}{(z + x_2)(z + x_0)}\right) \\\\
  &\geq \frac{2(|ε_1| + |ε_2|)^2}{3S} - \frac{3 |ε_1||ε_2|}{2}
    \left|\frac{y}{(y + x_1)(y + x_3)} - \frac{z}{(z + x_2)(z + x_0)}\right|.
\end{align*}
Both expressions inside the absolute value are non-negative and bounded above by
  $(y + z)^{-1} = S^{-1}$, so we get the desired bound
$$ L \geq \frac{2(|ε_1| + |ε_2|)^2}{3S} - \frac{3|ε_1||ε_2|}{2S}
  = \frac{4(|ε_1| + |ε_2|)^2 - 9|ε_1||ε_2|}{6S}. $$
-/

namespace IMOSL
namespace IMO2008A7

/-- The expression `∑_i (x_i - x_{i + 1})(x_i - x_{i + 2})/(x_i + x_{i + 1} + x_{i + 2})`. -/
def targetSum [Field F] (x : Fin 4 → F) : F :=
  (x 0 - x 1) * (x 0 - x 2) / (x 0 + x 1 + x 2)
  + (x 1 - x 2) * (x 1 - x 3) / (x 1 + x 2 + x 3)
  + (x 2 - x 3) * (x 2 - x 0) / (x 2 + x 3 + x 0)
  + (x 3 - x 0) * (x 3 - x 1) / (x 3 + x 0 + x 1)


variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Cauchy-Schwarz inequality, Engel form, in 2 variables. -/
theorem CauchySchwarzEngel2 (a b : F) (hc : c > 0) (hd : d > 0) :
    (a + b) ^ 2 / (c + d) ≤ a ^ 2 / c + b ^ 2 / d :=
  suffices (a + b) ^ 2 ≤ (a ^ 2 / c + b ^ 2 / d) * (c + d)
    from (div_le_iff₀ (add_pos hc hd)).mpr this
  calc (a + b) ^ 2
    _ = a ^ 2 + b ^ 2 + 2 * (a * b) := by rw [add_sq', mul_assoc]
    _ ≤ a ^ 2 + b ^ 2 + (a ^ 2 / c * d + b ^ 2 / d * c) :=
      have h : (a * b) ^ 2 = a ^ 2 / c * d * (b ^ 2 / d * c) := by
        rw [mul_mul_mul_comm, div_mul_div_comm, ← mul_pow, mul_comm d]
        exact (div_mul_cancel₀ _ (mul_pos hc hd).ne.symm).symm
      add_le_add_right (a := a ^ 2 + b ^ 2) <|
        two_mul_le_add_of_sq_eq_mul (mul_nonneg (div_nonneg (sq_nonneg a) hc.le) hd.le)
          (mul_nonneg (div_nonneg (sq_nonneg b) hd.le) hc.le) h
    _ = a ^ 2 / c * c + a ^ 2 / c * d + (b ^ 2 / d * d + b ^ 2 / d * c) := by
      rw [div_mul_cancel₀ _ hc.ne.symm, div_mul_cancel₀ _ hd.ne.symm, add_add_add_comm]
    _ = (a ^ 2 / c + b ^ 2 / d) * (c + d) := by
      rw [← mul_add, ← mul_add, add_comm d, ← add_mul]

/-- The estimate
  `(a - b)(a - c)/(a + b + c) + (c - d)(c - a)/(c + d + a) ≥ 2(a - c)^2/(2(a + c) + (b + d))`
  when `a + c + b > 0` and `a + c + d > 0`. -/
theorem two_term_estimate {a b c d : F} (hacb : a + c + b > 0) (hacd : a + c + d > 0) :
    2 * (a - c) ^ 2 / (2 * (a + c) + (b + d))
      - 3 * (a - c) * (b - d) / 2 * ((a + c) / ((a + c + b) * (a + c + d)))
      ≤ (a - b) * (a - c) / (a + b + c) + (c - d) * (c - a) / (c + d + a) :=
  calc 2 * (a - c) ^ 2 / (2 * (a + c) + (b + d))
        - 3 * (a - c) * (b - d) / 2 * ((a + c) / ((a + c + b) * (a + c + d)))
    _ = ((a - c) + (a - c)) ^ 2 / (2 * ((a + c + b) + (a + c + d)))
        - 3 * (a - c) * (b - d) / 2 * ((a + c) / ((a + c + b) * (a + c + d))) := by
      rw [sub_left_inj, ← two_mul, mul_pow, add_add_add_comm, ← two_mul, sq 2, mul_assoc]
      exact (mul_div_mul_left _ _ two_ne_zero).symm
    _ = (((a - c) + (a - c)) ^ 2 / ((a + c + b) + (a + c + d))
        - 3 * (a - c) * (b - d) * (a + c) / ((a + c + b) * (a + c + d))) / 2 := by
      rw [mul_comm 2, ← div_div, div_mul_div_comm, mul_comm 2, ← div_div, sub_div]
    _ ≤ ((a - c) ^ 2 / (a + c + b) + (a - c) ^ 2 / (a + c + d)
        - 3 * (a - c) * (b - d) * (a + c) / ((a + c + b) * (a + c + d))) / 2 :=
      div_le_div_of_nonneg_right (hc := zero_le_two)
        (sub_le_sub_right (CauchySchwarzEngel2 _ _ hacb hacd) _)
    _ = (a - b) * (a - c) / (a + c + b) + (c - d) * (c - a) / (a + c + d) := by
      field
    _ = (a - b) * (a - c) / (a + b + c) + (c - d) * (c - a) / (c + d + a) := by
      rw [add_right_comm a b c, add_rotate a c d]

/-- For any `a, b, c > 0`, we have `a/((a + b)(a + c)) < (a + b + c)⁻¹`. -/
theorem div_add_mul_add_lt {a b c : F} (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    a / ((a + b) * (a + c)) < (a + (b + c))⁻¹ := by
  have h : (a + b) * (a + c) > 0 := mul_pos (add_pos ha hb) (add_pos ha hc)
  have h0 : a + (b + c) > 0 := add_pos ha (add_pos hb hc)
  have h1 : (a + b) * (a + c) - a * (a + (b + c)) = b * c := by ring1
  rw [← one_div, div_lt_div_iff₀ h h0, one_mul, ← sub_pos, h1]
  exact mul_pos hb hc

/-- The estimate `|(a + c)/((a + c + b)(a + c + d)) - (b + d)/((b + d + c)(b + d + a))|
  < 1/((a + c) + (b + d))`. -/
theorem abs_sub_estimate {x : Fin 4 → F} (hx : ∀ i, x i > 0) :
    |(x 0 + x 2) / ((x 0 + x 2 + x 1) * (x 0 + x 2 + x 3))
      - (x 1 + x 3) / ((x 1 + x 3 + x 2) * (x 1 + x 3 + x 0))|
      < ((x 0 + x 2) + (x 1 + x 3))⁻¹ := by
  have hx02 : x 0 + x 2 > 0 := add_pos (hx 0) (hx 2)
  have hx13 : x 1 + x 3 > 0 := add_pos (hx 1) (hx 3)
  refine abs_sub_lt_of_nonneg_of_lt
    (div_pos hx02 (mul_pos (add_pos hx02 (hx 1)) (add_pos hx02 (hx 3)))).le
    (div_add_mul_add_lt hx02 (hx 1) (hx 3))
    (div_pos hx13 (mul_pos (add_pos hx13 (hx 2)) (add_pos hx13 (hx 0)))).le
    ((div_add_mul_add_lt hx13 (hx 2) (hx 0)).trans_eq ?_)
  rw [add_comm (x 2), add_comm]

/-- The main inequality. -/
theorem main_ineq {x : Fin 4 → F} (hx : ∀ i, x i > 0) :
    let ε₁ : F := x 0 - x 2
    let ε₂ : F := x 1 - x 3
    let y : F := x 0 + x 2
    let z : F := x 1 + x 3
    let S : F := y + z
    (4 * (|ε₁| + |ε₂|) ^ 2 - 9 * (|ε₁| * |ε₂|)) / (6 * S) ≤ targetSum x := by
  intro ε₁ ε₂ y z S
  have X2 : (2 : F) > 0 := two_pos
  have hy : y > 0 := add_pos (hx _) (hx _)
  have hz : z > 0 := add_pos (hx _) (hx _)
  calc targetSum x
    _ = ((x 0 - x 1) * (x 0 - x 2) / (x 0 + x 1 + x 2)
          + (x 2 - x 3) * (x 2 - x 0) / (x 2 + x 3 + x 0))
          + ((x 1 - x 2) * (x 1 - x 3) / (x 1 + x 2 + x 3)
            + (x 3 - x 0) * (x 3 - x 1) / (x 3 + x 0 + x 1)) := by
      rw [targetSum, add_assoc, add_add_add_comm]
    _ ≥ (2 * ε₁ ^ 2 / (2 * y + z) - 3 * ε₁ * ε₂ / 2 * (y / ((y + x 1) * (y + x 3))))
        + (2 * ε₂ ^ 2 / (2 * z + (x 2 + x 0))
          - 3 * ε₂ * (x 2 - x 0) / 2 * (z / ((z + x 2) * (z + x 0)))) :=
      add_le_add (two_term_estimate (add_pos hy (hx _)) (add_pos hy (hx _)))
        (two_term_estimate (add_pos hz (hx _)) (add_pos hz (hx _)))
    _ = 2 * (|ε₁| ^ 2 / (2 * y + z) + |ε₂| ^ 2 / (2 * z + y))
        - 3 * ε₁ * ε₂ / 2 * (y / ((y + x 1) * (y + x 3)) - z / ((z + x 2) * (z + x 0))) := by
      rw [sq_abs, sq_abs]; ring1
    _ ≥ 2 * ((|ε₁| + |ε₂|) ^ 2 / (2 * y + z + (2 * z + y)))
        - |3 * ε₁ * ε₂ / 2 * (y / ((y + x 1) * (y + x 3)) - z / ((z + x 2) * (z + x 0)))| :=
      sub_le_sub (hcd := le_abs_self _) <| mul_le_mul_of_nonneg_left (ha := X2.le) <|
        CauchySchwarzEngel2 _ _ (add_pos (mul_pos X2 hy) hz) (add_pos (mul_pos X2 hz) hy)
    _ = 2 * 2 * (|ε₁| + |ε₂|) ^ 2 / (2 * (2 + 1) * S)
        - |3 * ε₁ * ε₂ / 2| * |y / ((y + x 1) * (y + x 3)) - z / ((z + x 2) * (z + x 0))| := by
      rw [abs_mul, sub_left_inj, mul_assoc, mul_assoc, mul_div_mul_left _ _ X2.ne.symm,
        add_add_add_comm, ← mul_add, add_comm z, mul_div_assoc, ← add_one_mul]
    _ ≥ 2 * 2 * (|ε₁| + |ε₂|) ^ 2 / (2 * (2 + 1) * S) - |3 * ε₁ * ε₂ / 2| * S⁻¹ :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left (abs_sub_estimate hx).le (abs_nonneg _)) _
    _ = 4 * (|ε₁| + |ε₂|) ^ 2 / (2 * 3 * S) - 3 * |ε₁| * |ε₂| / 2 * (3 / (3 * S)) := by
      have X3 : (3 : F) > 0 := three_pos
      rw [two_add_one_eq_three, two_mul, two_add_two_eq_four, sub_right_inj, abs_div, abs_mul,
        abs_mul, abs_of_nonneg X3.le, abs_of_nonneg X2.le, div_mul_cancel_left₀ X3.ne.symm]
    _ = (4 * (|ε₁| + |ε₂|) ^ 2 - 9 * (|ε₁| * |ε₂|)) / (6 * S) := by
      have X6 : (2 : F) * 3 = 6 := by norm_num
      have X9 : (3 : F) * 3 = 9 := by norm_num
      rw [div_mul_div_comm, ← mul_assoc, X6, mul_assoc 3, mul_right_comm, X9, sub_div]

/-- The bound `4(x + y)^2 - 9xy ≥ (x + y)^2`, weakening the
  lower bound in the main inequality to `(|ε₁| + |ε₂|)^2/(6S)`. -/
theorem bound_weakening (x y : F) :
    (x + y) ^ 2 ≤ 4 * (x + y) ^ 2 - 9 * (x * y) := by
  have h : 4 * (4 * (x + y) ^ 2 - 9 * (x * y) - (x + y) ^ 2)
      = 3 * (x + y) ^ 2 + (3 * (x - y)) ^ 2 := by ring1
  rw [← sub_nonneg, ← mul_nonneg_iff_of_pos_left four_pos, h]
  exact add_nonneg (mul_nonneg zero_le_three (sq_nonneg _)) (sq_nonneg _)

/-- Final solution, part 1 -/
theorem final_solution_part1 {x : Fin 4 → F} (hx : ∀ i, x i > 0) : 0 ≤ targetSum x :=
  (main_ineq hx).trans' <| div_nonneg ((sq_nonneg _).trans (bound_weakening _ _)) <|
    mul_nonneg (by norm_num : 0 ≤ (6 : F)) <|
      add_nonneg (add_pos (hx 0) (hx 2)).le (add_pos (hx 1) (hx 3)).le

/-- Final solution, part 2 -/
theorem final_solution_part2 {x : Fin 4 → F} (hx : ∀ i, x i > 0) :
    targetSum x = 0 ↔ x 0 = x 2 ∧ x 1 = x 3 := by
  ---- The `←` direction is easy.
  refine Iff.symm ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · simp_rw [targetSum, h.1, h.2, sub_self, mul_zero, zero_div, add_zero]
  ---- The `→` direction follows from the bound we have proved; it implies `|ε₁| + |ε₂| = 0`.
  let ε₁ : F := x 0 - x 2
  let ε₂ : F := x 1 - x 3
  let T : F := 6 * ((x 0 + x 2) + (x 1 + x 3))
  have hT : T > 0 :=
    mul_pos (by norm_num) (add_pos (add_pos (hx 0) (hx 2)) (add_pos (hx 1) (hx 3)))
  replace h : (4 * (|ε₁| + |ε₂|) ^ 2 - 9 * (|ε₁| * |ε₂|)) / T ≤ 0 := (main_ineq hx).trans h.le
  replace h : 4 * (|ε₁| + |ε₂|) ^ 2 - 9 * (|ε₁| * |ε₂|) ≤ 0 := by
    rwa [div_nonpos_iff, or_iff_right λ h0 ↦ hT.not_ge h0.2, and_iff_left hT.le] at h
  replace h : (|ε₁| + |ε₂|) ^ 2 = 0 :=
    le_antisymm ((bound_weakening _ _).trans h) (sq_nonneg _)
  rw [sq_eq_zero_iff, add_eq_zero_iff_of_nonneg (abs_nonneg _) (abs_nonneg _)] at h
  exact h.imp eq_of_abs_sub_eq_zero eq_of_abs_sub_eq_zero
