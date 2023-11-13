import IMOSLLean4.IMO2012.A5.Case2.Subcase2
import IMOSLLean4.IMO2012.A5.Case2.Subcase3
import IMOSLLean4.IMO2012.A5.Case2.Subcase4

/-!
# IMO 2012 A5, Case 2: `f(-1) = 0` (Main File)

This file collects solutions to all subcases of Case 2.
-/

namespace IMOSL
namespace IMO2012A5

variable {R : Type _} [CommRing R]

/-- Main claim -/
theorem case2_map_two_cases [CommRing S] [IsDomain S]
    {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 0 = -1) :
    f 2 = 1 ∨ f 2 = -1 ∨ f 2 = 3 ∨ f 2 = 0 := by
  -- `f(3) = f(2)^2 - 1`
  have h2 := case2_map_sq_sub_one h h0 h1 2
  rw [sq, two_mul, ← one_add_one_eq_two, ← add_assoc,
    add_sub_cancel, one_add_one_eq_two] at h2
  rw [← or_assoc, ← sq_eq_sq_iff_eq_or_eq_neg, one_pow, ← sub_eq_zero, ← h2]
  -- `f(4) = (f(2) - 1) f(3) - 1`
  have h3 := case2_map_add_two_eq h h0
  have h4 := h3 (1 + 1)
  rw [add_sub_cancel, good_map_one h, add_zero, one_add_one_eq_two, mul_sub, ← sq,
    ← sub_sub_sub_cancel_right _ _ 1, ← h2, sub_right_comm, ← sub_one_mul] at h4
  -- `f(5) = f(2) f(3) = f(2) (f(2) - 2) f(3)`
  replace h2 := case2_map_self_mul_add_one_sub_one h h0 (1 + 1)
  rw [mul_add_one (1 + 1 : R), ← add_assoc,
    add_sub_cancel, one_add_one_eq_two] at h2
  specialize h3 (2 + 1)
  rwa [add_sub_cancel, add_right_comm, ← two_mul, h2, add_assoc, one_add_one_eq_two,
    ← mul_add_one (f 2), ← add_sub_right_comm, h4, sub_add_cancel, ← sub_one_mul,
    mul_eq_mul_left_iff, eq_comm, mul_left_eq_self₀, sub_sub, one_add_one_eq_two,
    sub_eq_iff_eq_add', two_add_one_eq_three, or_assoc, or_left_comm] at h3



variable {S : Type _} [Field S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 0 = -1)

theorem case2_quot_IsAnswer (h2 : ∀ c ∈ periodIdeal h, c = 0) : IsAnswer f := by
  rcases eq_or_ne (f 2) (-1) with h3 | h3
  · exact case2_4_quot_IsAnswer h h0 h3 h2
  rcases eq_or_ne (f 2) 1 with h4 | h4
  · exact case2_2_quot_IsAnswer h h0 h4 h3 h2
  rcases eq_or_ne (f 2) 3 with h5 | h5
  · exact case2_3_IsAnswer h h0 h5 h4 h1
  · have h6 := case2_map_two_cases h h0 h1
    rw [or_iff_right h4, or_iff_right h3, or_iff_right h5] at h6
    exact case2_1_quot_IsAnswer h h0 h6 h2 h1 h5

theorem case2_IsAnswer : IsAnswer f :=
  IsAnswer_of_periodLift h <|
    case2_quot_IsAnswer (periodLift_is_good h) h0 h1 (zero_of_periodic_periodLift h)
