/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.Case2.Basic
import IMOSLLean4.IMO2012.A5.A5Quotient

/-!
# IMO 2012 A5, Subcase 2.1: $f(-1) = 0$ and $f(2) = 0 ≠ 3$

This file solves Subcase 2.1.
-/

namespace IMOSL
namespace IMO2012A5

variable [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0)

/-- If `f(2) = 0`, then `3 ∈ I` -/
theorem case2_1_lem1 (h1 : f 2 = 0) : 3 ∈ periodIdeal h := λ x ↦ by
  rw [← two_add_one_eq_three, add_rotate, case2_map_add_two_eq h h0,
    h1, zero_mul, zero_add, add_sub_cancel_left]


section ThreeEqZero

variable (h1 : (3 : R) = 0)

/-- (7.1) -/
theorem case2_1_lem2 (x : R) : f x * f (x + 1) - f (x - 1) ^ 2 = f (x - 1) := by
  rw [← two_add_one_eq_three, add_eq_zero_iff_eq_neg] at h1
  have h2 := case2_special_identity h h0 x
  rwa [h1, h0, mul_zero, zero_add, ← sub_eq_add_neg, ← sq] at h2

/-- (7.1) with `x` replaced by `x + 1` -/
theorem case2_1_lem3 (x : R) : f (x + 1) * f (x - 1) - f x ^ 2 = f x := by
  have h2 := case2_1_lem2 h h0 h1 (x + 1)
  rw [← two_add_one_eq_three, add_eq_zero_iff_eq_neg] at h1
  rwa [add_sub_cancel_right, add_assoc,
    one_add_one_eq_two, h1, ← sub_eq_add_neg] at h2

/-- (7.2) -/
theorem case2_1_lem4 (x : R) :
    f (x - 1) + f x + f (x + 1) = -1 ∨ f x = f (x - 1) := by
  have h2 : _ - _ = _ - _ :=
    congr_arg₂ _ (case2_1_lem2 h h0 h1 x) (case2_1_lem3 h h0 h1 x)
  rwa [sub_sub_sub_comm, mul_comm, ← mul_sub, sub_eq_iff_eq_add,
    sq_sub_sq, ← one_add_mul (α := S), ← neg_sub (f x), mul_neg,
    ← neg_mul, mul_eq_mul_right_iff, sub_eq_zero, eq_neg_iff_add_eq_zero,
    add_comm, add_assoc, add_eq_zero_iff_neg_eq, eq_comm] at h2

/-- (7.3) -/
theorem case2_1_lem5 {c : R} (h2 : f (c + 1) = 0) (h3 : f (c - 1) = 0) :
    c ∈ periodIdeal h := λ x ↦ by
  rw [← two_add_one_eq_three, add_eq_zero_iff_eq_neg, ← one_add_one_eq_two] at h1
  let y := x - c - 1 - 1
  -- `f (y (c - 1) + (c + 1)) = f (y + 2 - c)`
  have h4 := case2_good_alt h h0 (y + 1) (c - 1)
  rw [h3, mul_zero, sub_eq_zero, add_one_mul y,
    add_sub_assoc, sub_sub, h1, sub_neg_eq_add] at h4
  -- `f (y (c + 1) + (c - 1)) = f (y + 2 + c)`
  have h5 := h (y * (c - 1)) (c + 1)
  rw [h2, mul_zero, sub_eq_zero, h4, mul_right_comm,
    eq_add_of_sub_eq (h _ _), h3, mul_zero, zero_add] at h5
  -- Finish by expressing `f(y (c^2 - 1) + 1)` in two ways
  replace h4 := h (y + 1) (c + 1)
  rwa [h2, mul_zero, sub_eq_zero, add_one_mul y, add_assoc, add_assoc,
    h1, ← sub_eq_add_neg, h5, sub_add_cancel, sub_sub_sub_cancel_right,
    sub_add_add_cancel, sub_add_cancel, sub_sub, ← two_mul,
    ← one_add_one_eq_two, h1, neg_one_mul, sub_neg_eq_add, add_comm] at h4

end ThreeEqZero


section Quotient

variable (h1 : f 2 = 0) (h2 : ∀ c ∈ periodIdeal h, c = 0)
  (h3 : f 0 = -1) (h4 : f 2 ≠ 3)

/-- (7.4) -/
theorem case2_1_lem6 (x : R) : f (x - 1) + f x + f (x + 1) = -1 := by
  -- Restrict to case `f(x) = f(x - 1)`
  replace h4 := h2 3 (case2_1_lem1 h h0 h1)
  have h5 := case2_1_lem4 h h0 h4
  refine (h5 x).elim id λ h6 ↦ ?_
  -- Restrict to case `f(x) = f(x - 1) = f(x + 1)`
  replace h2 : (1 + 1 : R) = -1 := by
    rwa [one_add_one_eq_two, eq_neg_iff_add_eq_zero, two_add_one_eq_three]
  have h7 := h5 (x - 1)
  rw [sub_add_cancel, sub_sub, h2, sub_neg_eq_add, add_rotate] at h7
  refine h7.resolve_right λ h7 ↦ ?_
  -- Get `f(x) = f(x - 1) = f(x + 1) = 0` and a contradiction
  have h8 := case2_1_lem2 h h0 h4 x
  rw [← h7, h6, ← sq, sub_self, eq_comm] at h8
  have h9 := case2_1_lem5 h h0 h4 (h7.symm.trans h8) h8 0
  rw [add_zero, h6, h8, h3, zero_eq_neg] at h9
  exact one_ne_zero h9

/-- (7.5) -/
theorem case2_1_lem7 (x : R) : f x = -1 ∨ f x = 0 := by
  have h7 := h2 3 (case2_1_lem1 h h0 h1)
  have h5 : (2 : R) = -1 := by rwa [eq_neg_iff_add_eq_zero, two_add_one_eq_three]
  -- `f(x^2) = f(x)^2 + f(x) + f(-x)`
  have h6 := h (x + 1) (x - 1)
  rw [← sq_sub_sq, one_pow, sub_add_cancel, add_add_sub_cancel,
    ← two_mul, h5, eq_add_of_sub_eq (case2_1_lem3 h h0 h7 _),
    neg_one_mul, add_comm, sub_eq_iff_eq_add, add_assoc] at h6
  -- `f(x^2 + 1) = f(x)^2 + f(-x)`
  replace h7 := h x x
  rw [← sq, ← two_mul, ← sq, h5, neg_one_mul, sub_eq_iff_eq_add] at h7
  -- Plug into (7.4): `f(x^2 - 1) + f(x^2) + f(x^2 + 1) = -1`
  replace h5 := case2_1_lem6 h h0 h1 h2 h3 (x ^ 2)
  rw [case2_map_sq_sub_one h h0 h3 x, h6, h7, case2_map_even h h0,
    ← two_mul, add_rotate, add_add_add_comm, ← two_mul, ← add_sub_assoc,
    sub_eq_neg_self, add_right_comm, ← add_one_mul (2 : S), sq,
    ← add_one_mul (2 : S), ← mul_add, two_add_one_eq_three, mul_eq_zero,
    ← add_one_mul (f x), mul_eq_zero, add_eq_zero_iff_eq_neg] at h5
  exact h5.resolve_left (h4.symm.trans_eq h1)

/-- (7.6) -/
theorem case2_1_lem8 (x : R) (h5 : f x = -1) : x = 0 := by
  replace h3 := case2_1_lem6 h h0 h1 h2 h3 x
  rw [h5, add_right_comm, add_left_eq_self] at h3
  have h6 := eq_add_of_sub_eq' (case2_1_lem3 h h0 (h2 3 <| case2_1_lem1 h h0 h1) x)
  rw [sq, ← add_one_mul (f x), mul_eq_zero_of_left (add_eq_zero_iff_eq_neg.mpr h5),
    eq_neg_of_add_eq_zero_left h3, mul_neg, neg_eq_zero, mul_self_eq_zero] at h6
  rw [h6, add_zero] at h3
  exact h2 x (case2_1_lem5 h h0 (h2 3 <| case2_1_lem1 h h0 h1) h6 h3)

/-- The main lemma for the subcase -/
theorem case2_1_lem9 (x : R) : x = 0 ∨ x = 1 ∨ x = -1 := by
  have h5 := case2_1_lem8 h h0 h1 h2 h3
  have h6 := case2_1_lem7 h h0 h1 h2 h3 h4
  refine (h6 x).imp (h5 x) (λ h7 ↦ ?_)
  refine (h6 (x - 1)).imp (λ h8 ↦ eq_of_sub_eq_zero (h5 _ h8)) (λ h8 ↦ ?_)
  replace h6 := case2_1_lem6 h h0 h1 h2 h3 x
  rw [h8, zero_add, h7, zero_add] at h6
  exact eq_neg_of_add_eq_zero_left (h5 _ h6)

/-- Solution for the current subcase (`𝔽₃Map2`) -/
theorem case2_1_quot_IsAnswer : IsAnswer f :=
  -- `𝔽₃ → R/I` is bijective
  have X : Function.Bijective (𝔽₃.castHom <| h2 3 <| case2_1_lem1 h h0 h1) :=
    ⟨𝔽₃.castHom_injective _ (one_ne_zero_of_map_zero h h3),
    λ x ↦ by rcases case2_1_lem9 h h0 h1 h2 h3 h4 x with h5 | h5 | h5
             exacts [⟨𝔽₃.𝔽₃0, h5.symm⟩, ⟨𝔽₃.𝔽₃1, h5.symm⟩, ⟨𝔽₃.𝔽₃2, h5.symm⟩]⟩
  -- Factor `f` out as `𝔽₃Map2 ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₃Map2 S ∘ π.toFun
    from this.symm ▸ IsAnswer.𝔽₃_map2_comp π.toRingHom π.surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | 𝔽₃.𝔽₃0 => h3
      | 𝔽₃.𝔽₃1 => good_map_one h
      | 𝔽₃.𝔽₃2 => h0

end Quotient
