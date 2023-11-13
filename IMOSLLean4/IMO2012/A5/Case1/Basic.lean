import IMOSLLean4.IMO2012.A5.A5Basic
import Mathlib.Algebra.GroupPower.Ring

/-!
# IMO 2012 A5, Case 1: `f(-1) ≠ 0` (Basic Results)

This file collects basic results in Case 1.
-/

namespace IMOSL
namespace IMO2012A5

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) ≠ 0)

/-- (3.5) The lemma depends only on `good f`, but is useless in the case `f = 0`. -/
theorem case1_map_add_main_eq1 (x y : R) :
    f (x + y) - f (-(x + y)) = f (-x) * f (-y) - f x * f y :=
  by rw [← h, ← h, neg_mul_neg, sub_sub_sub_cancel_left, ← neg_add]

/-- (3.6) The lemma depends only on `good f`, but is useless in the case `f = 0`. -/
theorem case1_map_add_main_eq2 (x y : R) :
    -(f (x + y + 1) * f (-1)) = f (-x) * f (-y) - f x * f y :=
  by rw [← case1_map_add_main_eq1 h, ← map_neg_sub_map2 h, neg_sub]

/-- (3.1) -/
theorem case1_map_neg_add_one (x : R) : f (-x + 1) = -f (x + 1) :=
  mul_right_cancel₀ h0 <| let h1 := map_neg_sub_map2 h
    by rw [← h1, neg_mul, ← h1, neg_neg, neg_sub]

theorem case1_map_zero : f 0 = -1 :=
  by_contra λ h1 ↦ h0 <| congr_fun (eq_zero_of_map_zero_ne_neg_one h h1) _

/-- (3.2) -/
theorem case1_map_two : f 2 = 1 := by
  rw [← neg_inj, ← one_add_one_eq_two, ← case1_map_zero h h0,
    ← case1_map_neg_add_one h h0, neg_add_self]

/-- (3.3) -/
theorem case1_map_add_one_add_map_sub_one (x : R) :
    f (x + 1) + f (x - 1) = -(f x * f (-1)) := by
  rw [← neg_eq_iff_eq_neg, neg_add', ← map_neg_sub_map1 h,
    ← case1_map_neg_add_one h h0, neg_add_eq_sub x 1]

/-- (3.4) -/
theorem case1_map_two_mul_add_one (x : R) :
    f (2 * x + 1) = -(f (x + 1) * f (-1)) := by
  rw [← case1_map_add_one_add_map_sub_one h h0, add_sub_cancel, add_rotate,
    one_add_one_eq_two, ← sub_eq_iff_eq_add', h, case1_map_two h h0, one_mul]

/-- (3.7) -/
theorem case1_map_add_one_ne_zero_imp {x : R} (h1 : f (x + 1) ≠ 0) :
    f (-x) + f x = f (-1) := by
  have h2 := map_neg_sub_map2 h x
  apply mul_right_cancel₀ (b := f (-x) - f x)
  · rw [h2]; exact mul_ne_zero h1 h0
  · rw [← mul_self_sub_mul_self, ← case1_map_add_main_eq2 h, ← two_mul,
      ← neg_mul, h2, case1_map_two_mul_add_one h h0, neg_neg, mul_comm]

/-- (3.8) -/
theorem case1_map_add_one_eq_zero_imp {x : R} (h1 : f (x + 1) = 0) :
    f x = -1 ∧ f (-x) = -1 := by
  -- Reduce to `f(x) = -1` via `f(-x) = f(x)`
  have h2 : f (-x) = f x := by rw [← sub_eq_zero, map_neg_sub_map2 h, h1, zero_mul]
  rw [h2, and_self]
  -- Prove `f(x) f(-1) = f(x) f(-x - 1)`
  have h3 := case1_map_two_mul_add_one h h0
  have h4 := case1_map_add_main_eq1 h x (x + 1)
  rw [h1, mul_zero, sub_zero, ← add_assoc, ← two_mul, h3, h1, zero_mul,
    neg_zero, zero_sub, ← sub_add_cancel'' (1 : R), add_assoc,
    one_add_one_eq_two, ← mul_add_one _ x, ← neg_add_eq_sub, ← mul_neg,
    h3, neg_neg, neg_add_eq_sub, sub_add_cancel'', h2] at h4
  -- Finish with (3.6)
  have h5 := case1_map_add_main_eq2 h x (-(x + 1))
  rwa [neg_neg, h1, mul_zero, zero_sub, neg_inj, add_right_comm, add_neg_self,
    ← h4, mul_eq_mul_right_iff, case1_map_zero h h0, or_iff_left h0, eq_comm] at h5
