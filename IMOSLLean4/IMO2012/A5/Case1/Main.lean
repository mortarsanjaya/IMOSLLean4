import IMOSLLean4.IMO2012.A5.Case1.Subcase1
import IMOSLLean4.IMO2012.A5.Case1.Subcase2

/-!
# IMO 2012 A5, Case 1: `f(-1) ≠ 0` (Main File)

This file collects solutions to all subcases of Case 1.
-/

namespace IMOSL
namespace IMO2012A5

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) ≠ 0)

/-- Main claim -/
theorem case1_map_neg_one_cases : f (-1) = -2 ∨ f (-1) = 1 := by
  have h1 : -f (-1) = f (2 + 1) := by
    rw [neg_eq_iff_eq_neg, ← one_add_one_eq_two,
      ← case1_map_neg_add_one h h0, neg_add, neg_add_cancel_comm]
  have h2 : f 2 = 1 := case1_map_two h h0
  -- `f(4) = C^2 - 1`, where `C = f(-1)`
  have h3 := case1_map_add_one_add_map_sub_one h h0
  have h4 := h3 (2 + 1)
  rw [add_sub_cancel, h2, ← h1, neg_mul, neg_neg, ← eq_sub_iff_add_eq] at h4
  -- Double-evaluating `f(5)` gives `(C - 1) C = -(C^2 - 1) C`, where `C = f(-1)`
  have h5 := h3 (2 + 1 + 1)
  rw [add_sub_cancel, h4, ← h1, ← neg_mul, add_assoc (2 : R), ← one_add_one_eq_two,
    ← two_mul, eq_add_of_sub_eq (h _ _), ← add_assoc, h4, one_add_one_eq_two, h2,
    one_mul, add_sub_cancel'_right, ← sub_eq_add_neg, ← sub_one_mul] at h5
  -- Finishing
  replace h5 := mul_right_cancel₀ h0 h5
  replace h3 := sq_sub_sq (f (-1)) 1
  rwa [one_pow, sq, ← neg_eq_iff_eq_neg.mpr h5,
    ← neg_one_mul, mul_eq_mul_right_iff, sub_eq_zero, eq_comm,
    ← eq_sub_iff_add_eq, ← neg_add', one_add_one_eq_two] at h3

theorem case1_quot_IsAnswer (h1 : ∀ c ∈ periodIdeal h, c = 0) : IsAnswer f :=
  (eq_or_ne (f (-1)) (-2)).elim
    (case1_1_IsAnswer h h0)
    (λ h2 ↦ case1_2_quot_IsAnswer h h0 h2
      ((case1_map_neg_one_cases h h0).resolve_left h2) h1)

theorem case1_IsAnswer : IsAnswer f :=
  IsAnswer_of_periodLift h <|
    case1_quot_IsAnswer (periodLift_is_good h) h0 (zero_of_periodic_periodLift h)
