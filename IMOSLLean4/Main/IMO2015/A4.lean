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

### Answer

$f(x) = x$ and $f(x) = 2 - x$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2015SL.pdf).
We change $y f(x)$ to $f(x) y$ in our formulation as this makes the identity function
  a solution to the functional equation.
It is worth mentioning that the case $f(0) = 0$ works as long as $2$ is not a
  zero divisor in $R$, even without assuming that $R$ is a domain.

### Generalization

It is possible to solve the case where $R$ has characteristic $2$ as well.
The answer set is the same, or more precisely, just $x ↦ x$.
In the future, we may hope to lift off the domain assumption on $R$.
However, this is a far stretch.

See `IMOSLLean4/Generalization/IMO2015A4/IMO2015A4.lean` for the implementation.
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

/-- For any `x ∈ R`, we have `f(x + f(x + 1)) = x + f(x + 1)`. -/
theorem map_add_map_add_one_fixed {f : R → R} (hf : good f) (x) :
    f (x + f (x + 1)) = x + f (x + 1) := by
  have h := hf x 1
  rwa [mul_one, mul_one, add_left_inj] at h

/-- For any `y ∈ R`, we have `f(f(y)) + f(0) = f(y) + f(0) y`. -/
theorem map_map_add_map_zero {f : R → R} (hf : good f) (y) :
    f (f y) + f 0 = f y + f 0 * y := by
  have h := hf 0 y
  rwa [zero_add, zero_add, zero_mul] at h

/-- For any fixed point `y`, we have `f(0) (1 - y) = 0`. -/
theorem fixed_point_formula {f : R → R} (hf : good f) (hy : f y = y) :
    f 0 * (1 - y) = 0 := by
  have h := hf.map_map_add_map_zero y
  rwa [hy, hy, add_right_inj, ← sub_eq_zero, ← mul_one_sub] at h


section

variable [NoZeroDivisors R] {f : R → R} (hf : good f) (hf0 : f 0 ≠ 0)
include hf hf0

/-- If `R` is a domain and `f(0) ≠ 0`, then the only fixed point is `1`. -/
theorem fixed_point_eq_one (hy : f y = y) : y = 1 := by
  have h : f 0 * (1 - y) = 0 := hf.fixed_point_formula hy
  rwa [mul_eq_zero, or_iff_right hf0, sub_eq_zero, eq_comm] at h

/-- If `R` is a domain and `f(0) ≠ 0`, then `f(x) = 2 - x` for every `x ∈ R`. -/
theorem eq_two_sub_of_map_zero_ne_zero : f = (λ x ↦ 2 - x) := by
  -- Indeed, `x + f(x + 1)` is always a fixed point, so it is equal to `1`.
  funext x
  have h : x - 1 + f (x - 1 + 1) = 1 :=
    hf.fixed_point_eq_one hf0 (hf.map_add_map_add_one_fixed _)
  rwa [sub_add_cancel, ← eq_sub_iff_add_eq', sub_sub_eq_add_sub, one_add_one_eq_two] at h

end


/-- If `f(0) = 0`, then `f(-1) = -1`. -/
theorem neg_one_fixed_of_zero_fixed {f : R → R} (hf : good f) (hf0 : f 0 = 0) :
    f (-1) = -1 := by
  have h : f (-1 + f (-1 + 1)) = -1 + f (-1 + 1) := hf.map_add_map_add_one_fixed (-1)
  rwa [neg_add_cancel, hf0, add_zero] at h

/-- If `2` is not a zero divisor of `R` and `f(0) = 0`, then `f(1) = 1`. -/
theorem map_one_of_twoNZD_map_zero (hR : ∀ x y : R, 2 * x = 2 * y → x = y)
    {f : R → R} (hf : good f) (hf0 : f 0 = 0) : f 1 = 1 := by
  have h := hf 1 (-1)
  rw [add_neg_cancel, hf0, add_zero, one_mul, hf.neg_one_fixed_of_zero_fixed hf0,
    mul_neg_one, add_neg_eq_iff_eq_add, add_right_comm, eq_add_neg_iff_add_eq,
    ← two_mul, ← two_mul] at h
  exact hR _ _ h


section

variable {f : R → R} (hf : good f)
include hf

/-- For any `x ∈ R`, we have `f(x + f(x)) + f(0) = x + f(x)`. -/
theorem map_self_add_map_self (x) : f (x + f x) + f 0 = x + f x := by
  simpa only [add_zero, mul_zero] using hf x 0

/-- If `f(1) = 1`, then `f(1 + f(y + 1)) + f(y) = 1 + f(y + 1) + y`. -/
theorem map_one_add_map_add_one_of_map_one (hf1 : f 1 = 1) (y) :
    f (1 + f (y + 1)) + f y = 1 + f (y + 1) + y := by
  simpa only [add_comm y 1, one_mul, hf1] using hf 1 y

/-- If `f(1) = 1`, `f(y) = y`, and `f(y + 1) = y + 1`, then `f(y + 2) = y + 2`. -/
theorem fixed_pt_add_two_of_map_one
    (hf1 : f 1 = 1) (hy : f y = y) (hy1 : f (y + 1) = y + 1) :
    f (y + 2) = y + 2 := by
  have h : f (1 + f (y + 1)) + f y = 1 + f (y + 1) + y :=
    hf.map_one_add_map_add_one_of_map_one hf1 y
  rwa [hy1, hy, add_left_inj, add_left_comm, one_add_one_eq_two] at h

/-- If `f(0) = 0` and `f(1) = 1`, then `f(-x) = -f(x)` for all `x ∈ R`. -/
theorem map_neg_of_map_zero_map_one (hf0 : f 0 = 0) (hf1 : f 1 = 1) (x) :
    f (-x) = -f x := by
  ---- First change `x` to `x - 2` in `f(x + f(x + 1)) = x + f(x + 1)`.
  have h : f (x + f (x - 1) - (1 + 1)) = x + f (x - 1) - (1 + 1) := by
    have h := hf.map_add_map_add_one_fixed (x - 1 - 1)
    rwa [sub_add_cancel, sub_sub, ← add_sub_right_comm] at h
  ---- Now change `x` to `x - 1` in `f(x + f(x)) + f(0) = x + f(x)` and use `f(0) = 0`.
  have h0 : f (x + f (x - 1) - (1 + 1) + 1) = x + f (x - 1) - (1 + 1) + 1 := by
    rw [← sub_sub, sub_add_cancel, add_sub_right_comm,
      eq_sub_of_add_eq (hf.map_self_add_map_self _), hf0, sub_zero]
  ---- Then we applying the fixed point argument, we get `f(x + f(x - 1)) = x + f(x - 1)`.
  replace h : f (x + f (x - 1)) = x + f (x - 1) := by
    have h1 := hf.fixed_pt_add_two_of_map_one hf1 h h0
    rwa [one_add_one_eq_two, sub_add_cancel] at h1
  ---- Now substitute `y = -1` into the original FE and use the above equality.
  replace h0 : f (x + f (x + -1)) + f (x * -1) = x + f (x + -1) + f x * -1 := hf x (-1)
  rwa [← sub_eq_add_neg, h, add_right_inj, mul_neg_one, mul_neg_one] at h0

/-- If `f(0) = 0` and `f(1) = 1`, then `2 f(y) = 2y` for all `y ∈ R`. -/
theorem two_mul_map_of_map_zero_eq_zero (hf0 : f 0 = 0) (hf1 : f 1 = 1) (y) :
    2 * f y = 2 * y := by
  ---- Recall that `f(-x) = -f(x)` for all `x ∈ R`.
  have hf2 (x) : f (-x) = -f x := hf.map_neg_of_map_zero_map_one hf0 hf1 x
  ---- Also, recall that `f(1 + f(y + 1)) + f(y) = 1 + f(y + 1) + y`.
  have h : f (1 + f (y + 1)) + f y = 1 + f (y + 1) + y :=
    hf.map_one_add_map_add_one_of_map_one hf1 y
  ---- `(x, y) → (-1, -y)` gives `-f(1 + f(y + 1)) + f(y) = -(1 + f(y + 1)) + y`.
  have h0 : -f (1 + f (y + 1)) + f y = -(1 + f (y + 1)) + y := by
    have h0 := hf (-1) (-y)
    rwa [← neg_add_rev, hf2, ← neg_add, hf2, hf2, hf1, neg_mul_neg, one_mul] at h0
  ---- Now add these two equations and simplify.
  replace h : _ + _ = _ + _ := congrArg₂ (· + ·) h h0
  iterate 2 rw [← add_assoc, add_neg_cancel_comm, ← two_mul] at h
  exact h

end


/-- If `2` is not a zero divisor in `R` and `f(0) = 0`, then `f = id`. -/
theorem eq_id_of_map_zero_eq_zero2 (hR : ∀ x y : R, 2 * x = 2 * y → x = y)
    {f : R → R} (hf : good f) (hf0 : f 0 = 0) : f = id :=
  funext λ y ↦ hR _ _
    (hf.two_mul_map_of_map_zero_eq_zero hf0 (map_one_of_twoNZD_map_zero hR hf hf0) y)

end good


/-- Final solution -/
theorem final_solution [DecidableEq R] [NoZeroDivisors R] (hR : (2 : R) ≠ 0) {f : R → R} :
    good f ↔ f = (λ x ↦ 2 - x) ∨ f = id := by
  refine ⟨λ hf ↦ ?_, λ hf ↦ ?_⟩
  ---- The `→` direction.
  · refine (Decidable.em (f 0 = 0)).symm.imp hf.eq_two_sub_of_map_zero_ne_zero
      (hf.eq_id_of_map_zero_eq_zero2 λ x y h ↦ ?_)
    -- We just need to show that `2 ≠ 0` implies that `2` is not a zero divisor.
    rw [← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h
    exact h.resolve_left hR
  ---- The `←` direction.
  · rcases hf with rfl | rfl
    exacts [two_sub_is_good, id_is_good]
