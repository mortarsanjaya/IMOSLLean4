/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.Case1.Basic
import IMOSLLean4.IMO2012.A5.A5Quotient

/-!
# IMO 2012 A5, Subcase 1.2: $f(-1) = 1 ≠ -2$

This file solves Subcase 1.2.
-/

namespace IMOSL
namespace IMO2012A5

variable [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) ≠ 0) (h1 : f (-1) ≠ -2)
    (h2 : f (-1) = 1) (h3 : ∀ c ∈ periodIdeal h, c = 0)

/-- (5.1) -/
theorem case1_2_lem1 (h1 : ∀ c ∈ periodIdeal h, c = 0)
    (h2 : f (c + 1) = 0) : c = 0 :=
  h1 c λ x ↦ by
    have h4 := case1_map_add_main_eq2 h c (x - 1)
    have h5 := case1_map_add_one_eq_zero_imp h h0 h2
    rw [h5.1, h5.2, ← mul_sub, neg_one_mul, neg_inj, map_neg_sub_map2 h,
      add_assoc, sub_add_cancel, mul_eq_mul_right_iff] at h4
    exact h4.resolve_right h0

/-- (5.2) -/
theorem case1_2_lem2 (x : R) : f (x + 1) + f (x - 1) + f x = 0 := by
  rw [add_eq_zero_iff_eq_neg, case1_map_add_one_add_map_sub_one h h0, h2, mul_one]

/-- `3 = 0` in `R` -/
theorem case1_2_lem3 : (3 : R) = 0 :=
  h3 (3 : R) λ x ↦ by
    have h4 y : f (y + 1) = -f y - f (y - 1) :=
      eq_sub_of_add_eq <| eq_neg_of_add_eq_zero_left (case1_2_lem2 h h0 h2 y)
    rw [add_comm, ← two_add_one_eq_three, ← add_assoc, h4, ← one_add_one_eq_two,
      ← add_assoc, add_sub_cancel, ← neg_add', h4, add_sub_cancel,
      ← add_sub_right_comm, neg_add_self, zero_sub, neg_neg]

/-- (5.3) -/
theorem case1_2_lem4 (x : R) (h4 : x ≠ 0) : f (-x) + f x = 1 :=
  h2 ▸ case1_map_add_one_ne_zero_imp h h0 (mt (case1_2_lem1 h h0 h3) h4)

/-- The main lemma for the subcase -/
theorem case1_2_lem5 (x : R) : x = 0 ∨ x = 1 ∨ x = -1 := by
  by_contra h4
  rw [not_or, not_or, ← add_eq_zero_iff_eq_neg] at h4
  have h5 := case1_2_lem4 h h0 h2 h3
  have h6 := case1_2_lem2 h h0 h2
  replace h6 : _ + _ = 0 + 0 := congr_arg₂ (· + ·) (h6 (-x)) (h6 x)
  rw [add_zero, add_add_add_comm, h5 x h4.1, add_comm (f (x + 1)),
    add_add_add_comm, ← neg_add', h5 _ h4.2.2, neg_add_eq_sub, ← neg_sub,
    h5 _ (sub_ne_zero_of_ne h4.2.1), one_add_one_eq_two] at h6
  apply h1; rwa [h2, eq_neg_iff_add_eq_zero, add_comm]

/-- Solution for the current subcase (`𝔽₃Map1`) -/
theorem case1_2_quot_IsAnswer : IsAnswer f :=
  -- `𝔽₃ → R/I` is bijective
  have X : Function.Bijective (𝔽₃.castHom <| case1_2_lem3 h h0 h2 h3) :=
    ⟨𝔽₃.castHom_injective _ (one_ne_zero_of_map_zero h (case1_map_zero h h0)),
    λ x ↦ by rcases case1_2_lem5 h h0 h1 h2 h3 x with h4 | h4 | h4
             exacts [⟨𝔽₃.𝔽₃0, h4.symm⟩, ⟨𝔽₃.𝔽₃1, h4.symm⟩, ⟨𝔽₃.𝔽₃2, h4.symm⟩]⟩
  -- Factor `f` out as `𝔽₃Map1 ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₃Map1 S ∘ π.toFun
    from this.symm ▸ IsAnswer.𝔽₃_map1_comp π.toRingHom π.surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | 𝔽₃.𝔽₃0 => case1_map_zero h h0
      | 𝔽₃.𝔽₃1 => good_map_one h
      | 𝔽₃.𝔽₃2 => h2
