/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic

/-!
# IMO 2015 A4 (P5)

Let $R$ be a (not necessarily commutative) domain such that $2 ≠ 0$ in $R$.
Find all functions $f : R → R$ such that for any $x, y ∈ R$,
$$ f(x + f(x + y)) + f(xy) = x + f(x + y) + f(x) y. $$

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2015SL.pdf).
We change $y f(x)$ to $f(x) y$ in our formulation as this makes the identity function
  a solution to the functional equation.
We define a function to be `good` if it satisfies the given functional equation.
-/

namespace IMOSL
namespace IMO2015A4

variable [Ring R]

/-- A function `f : R → R` is good if for any `x, y ∈ R`,
  we have `f(x + f(x + y)) + f(xy) = x + f(x + y) + f(x) y`. -/
def good (f : R → R) := ∀ x y, f (x + f (x + y)) + f (x * y) = x + f (x + y) + f x * y

/-- The identity function is good. -/
theorem id_is_good : good (id : R → R) :=
  λ _ _ ↦ rfl

/-- The function `x ↦ 2 - x` is good. -/
theorem two_sub_is_good : good (λ x : R ↦ 2 - x) := by
  intro x y
  have h : x + (2 - (x + y)) = 2 - y := by rw [← add_sub_assoc, add_sub_add_left_eq_sub]
  calc 2 - (x + (2 - (x + y))) + (2 - x * y)
    _ = y + 2 - x * y := by rw [h, sub_sub_cancel, add_sub_assoc]
    _ = 2 * y + (2 - y) - x * y := by rw [two_mul, add_add_sub_cancel]
    _ = 2 - y + (2 - x) * y := by rw [add_sub_assoc, add_sub_left_comm, sub_mul]
    _ = x + (2 - (x + y)) + (2 - x) * y := by rw [h]


namespace good

variable {f : R → R} (hf : good f)
include hf

/-- For any `x ∈ R`, we have `f(x + f(x + 1)) = x + f(x + 1)`. -/
theorem map_add_map_add_one_fixed (x) : f (x + f (x + 1)) = x + f (x + 1) := by
  have h := hf x 1
  rwa [mul_one, mul_one, add_left_inj] at h

/-- For any fixed point `y`, we have `f(0) (1 - y) = 0`. -/
theorem fixed_point_formula {y} (hy : f y = y) : f 0 * (1 - y) = 0 := by
  have h := hf 0 y
  rw [zero_add, zero_add, hy, hy, zero_mul, add_right_inj] at h
  rwa [mul_one_sub, sub_eq_zero]

omit f hf in
/-- If `R` is a domain and `f(0) ≠ 0`, then the only fixed point is `1`. -/
theorem fixed_point_eq_one [NoZeroDivisors R]
    {f : R → R} (hf : good f) (hf0 : f 0 ≠ 0) {y} (hy : f y = y) : y = 1 := by
  have h : f 0 * (1 - y) = 0 := hf.fixed_point_formula hy
  rwa [mul_eq_zero, or_iff_right hf0, sub_eq_zero, eq_comm] at h

/-- If `f(0) ≠ 0`, then `f(x) = 2 - x` for every `x ∈ R`. -/
theorem eq_two_sub_of_map_zero_ne_zero [NoZeroDivisors R] (hf0 : f 0 ≠ 0) :
    f = (λ x ↦ 2 - x) :=
  -- Indeed, `x + f(x + 1)` is always a fixed point, so it is equal to `1`.
  funext λ x ↦ calc f x
    _ = f (x - 1 + 1) := by rw [sub_add_cancel]
    _ = 1 - (x - 1) :=
      eq_sub_of_add_eq' <| hf.fixed_point_eq_one hf0 <| hf.map_add_map_add_one_fixed _
    _ = 2 - x := by rw [sub_sub_eq_add_sub, one_add_one_eq_two]

/-- If `f(0) = 0`, then `f(-1) = -1`. -/
theorem neg_one_fixed_of_zero_fixed (hf0 : f 0 = 0) : f (-1) = -1 := by
  have h : f (-1 + f (-1 + 1)) = -1 + f (-1 + 1) := hf.map_add_map_add_one_fixed (-1)
  rwa [neg_add_cancel, hf0, add_zero] at h

omit f hf in
/-- If `2` is not a zero divisor in `R` and `f(0) = 0`, then `f = id`. -/
theorem eq_id_of_map_zero_eq_zero (hR : ∀ x y : R, 2 * x = 2 * y → x = y)
    {f : R → R} (hf : good f) (hf0 : f 0 = 0) : f = id := by
  have hf1 : f (-1) = -1 := hf.neg_one_fixed_of_zero_fixed hf0
  ---- First get the formula `f(1 + f(y + 1)) + f(y) = 1 + f(y + 1) + y f(1)`.
  have h (y) : f (1 + f (y + 1)) + f y = 1 + f (y + 1) + f 1 * y := by
    simpa only [add_comm y 1, one_mul] using hf 1 y
  ---- Now get `f(1) = 1` by plugging `y = -1` into the above formula.
  have h0 : f 1 = 1 := by
    have h0 : f (1 + f (-1 + 1)) + f (-1) = 1 + f (-1 + 1) + f 1 * (-1) := h (-1)
    rw [neg_add_cancel, hf0, add_zero, hf1, mul_neg_one, add_neg_eq_iff_eq_add,
      add_right_comm, eq_add_neg_iff_add_eq, ← two_mul, ← two_mul] at h0
    exact hR _ _ h0
  ---- Next, the previous equality reduces to `f(1 + f(y + 1)) + f(y) = 1 + f(y + 1) + y`.
  replace h (y) : f (1 + f (y + 1)) + f y = 1 + f (y + 1) + y := by rw [h, h0, one_mul]
  ---- In particular, if `f(y) = y` and `f(y + 1) = y + 1`, then `f(y + 2) = y + 2`.
  replace h0 {y} (hy : f y = y) (hy0 : f (y + 1) = y + 1) :
      f (y + (1 + 1)) = y + (1 + 1) := by
    specialize h y; rwa [hy, hy0, add_left_inj, add_left_comm] at h
  ---- Then we get `f(x + f(x + 1) + 2) = x + f(x + 1) + 2` for all `x ∈ R`.
  replace h0 (x) : f (x + f (x + 1) + (1 + 1)) = x + f (x + 1) + (1 + 1) := by
    -- It suffices to prove `f(x + f(x + 1) + 1) = x + f(x + 1) + 1`.
    refine h0 (hf.map_add_map_add_one_fixed x) ?_
    -- Now this follows from `(x, y) ↦ (x + 1, 0)` in the original FE.
    simpa only [add_right_comm x _ 1, add_zero, mul_zero, hf0] using hf (x + 1) 0
  ---- Change the equality to `f(x + f(x - 1)) = x + f(x - 1)`.
  replace h0 (x) : f (x + f (x - 1)) = x + f (x - 1) := by
    specialize h0 (x - (1 + 1))
    rwa [add_assoc, sub_add_add_cancel, ← sub_sub, sub_add_cancel] at h0
  ---- From the above, get `f(-x) = -f(x)` for all `x ∈ R`.
  replace h0 (x) : f (-x) = -f x := by
    have h1 := hf x (-1)
    rwa [← sub_eq_add_neg, mul_neg_one, h0, add_right_inj, mul_neg_one] at h1
  ---- Now fix `y`. Substitute `(x, y) ↦ (-1, -y)` into the original FE.
  funext y
  have h1 : -f (1 + f (y + 1)) + f y = -(1 + f (y + 1)) + y := by
    have h1 := hf (-1) (-y)
    rwa [← neg_add_rev, hf1, neg_mul_neg, one_mul, h0, ← neg_add, h0] at h1
  ---- Finally, adding into `f(1 + f(y + 1)) + f(y) = 1 + f(y + 1) + y`, we're done.
  apply hR
  calc 2 * f y
    _ = f (1 + f (y + 1)) + f y + (-f (1 + f (y + 1)) + f y) := by
      rw [add_add_add_comm, add_neg_cancel, zero_add, two_mul]
    _ = 1 + f (y + 1) + y + (-(1 + f (y + 1)) + y) := by rw [h, h1]
    _ = 2 * y := by rw [add_add_add_comm, add_neg_cancel, zero_add, two_mul]

end good


/-- Final solution -/
theorem final_solution [DecidableEq R] [NoZeroDivisors R] (hR : (2 : R) ≠ 0) {f : R → R} :
    good f ↔ f = (λ x ↦ 2 - x) ∨ f = id := by
  refine ⟨λ hf ↦ ?_, λ hf ↦ ?_⟩
  ---- The `→` direction.
  · refine (Decidable.em (f 0 = 0)).symm.imp hf.eq_two_sub_of_map_zero_ne_zero
      (hf.eq_id_of_map_zero_eq_zero λ x y h ↦ ?_)
    -- We just need to show that `2 ≠ 0` implies that `2` is not a zero divisor.
    rw [← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h
    exact h.resolve_left hR
  ---- The `←` direction.
  · rcases hf with rfl | rfl
    exacts [two_sub_is_good, id_is_good]
