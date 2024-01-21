/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Regular

/-!
# IMO 2012 A5 (Basic Results)

This file collects some basic results.
-/

namespace IMOSL
namespace IMO2012A5

variable [Ring R] [Ring R₀] [Ring S]

/-- Given `f : R → S` and `φ : R₀ →+* R` surjective,
  `f` is good if `f ∘ φ` is good. -/
theorem good_of_comp_hom_good_surjective {φ : R₀ →+* R}
    (h : Function.Surjective φ) {f : R → S} (h0 : good (f ∘ φ.toFun)) :
    good f := λ x y ↦ by
  rcases h x with ⟨a, rfl⟩
  rcases h y with ⟨b, rfl⟩
  rw [← φ.map_add, ← φ.map_mul, ← φ.map_one, ← φ.map_add]
  exact h0 a b

/-- Given `f : R → S` and `φ : R₀ →+* R` surjective,
  `f ∘ φ` is an answer if `f` is an answer. -/
theorem IsAnswer_comp_hom {φ : R₀ →+* R} (h : φ.toFun.Surjective)
    {f : R → S} (h0 : IsAnswer f) : IsAnswer (f ∘ φ.toFun) :=
  h0.recOn IsAnswer.of_zero
    (λ ρ ↦ IsAnswer.hom_sub_one (ρ.comp φ))
    (λ ρ ↦ IsAnswer.hom_sq_sub_one (ρ.comp φ))
    (λ ρ h1 ↦ IsAnswer.𝔽₂_map_comp (ρ.comp φ) (h1.comp h))
    (λ ρ h1 ↦ IsAnswer.𝔽₃_map1_comp (ρ.comp φ) (h1.comp h))
    (λ ρ h1 ↦ IsAnswer.𝔽₃_map2_comp (ρ.comp φ) (h1.comp h))
    (λ ρ h1 ↦ IsAnswer.ℤ₄_map_comp (ρ.comp φ) (h1.comp h))
    (λ ρ h1 ↦ IsAnswer.𝔽₂ε_map_comp (ρ.comp φ) (h1.comp h))
    (λ ρ h1 ↦ IsAnswer.𝔽₄_map_comp (ρ.comp φ) (h1.comp h))



variable [IsDomain S] {f : R → S} (h : good f)

theorem good_map_one : f 1 = 0 := by
  rw [← mul_self_eq_zero, ← h, mul_one, sub_self]

theorem neg_map_zero_mul (x : R) : -f 0 * f x = f x := by
  rw [neg_mul, neg_eq_iff_eq_neg, ← h, zero_mul,
    zero_add, good_map_one h, zero_sub, zero_add]

/-- (1.1) -/
theorem eq_zero_of_map_zero_ne_neg_one (h0 : f 0 ≠ -1) : f = 0 :=
  funext λ x ↦ (mul_left_eq_self₀.mp <| neg_map_zero_mul h x).resolve_left
    λ h1 ↦ h0 <| neg_eq_iff_eq_neg.mp h1

theorem one_ne_zero_of_map_zero (h0 : f 0 = -1) : (1 : R) ≠ 0 :=
  mt (congr_arg f) <| by rw [good_map_one h, h0, zero_eq_neg]; exact one_ne_zero

/-- (1.2) -/
theorem map_neg_sub_map1 (x : R) : f (1 - x) - f (x - 1) = f x * f (-1) := by
  rw [← h, mul_neg_one, neg_add_eq_sub, ← sub_eq_add_neg]

/-- (1.3) -/
theorem map_neg_sub_map2 (x : R) : f (-x) - f x = f (x + 1) * f (-1) := by
  rw [← map_neg_sub_map1 h, sub_add_cancel'', add_sub_cancel]

/-- Auxiliary lemma for two sub-cases -/
theorem eq_hom_sub_one_of (h0 : ∀ x y, f (x + y) = f x + f y + 1) :
    ∃ φ : R →+* S, f = (φ.toFun · - 1) :=
  let g := (f · + 1)
  have h1 : f 1 = 0 := good_map_one h
  have h2 : g 1 = 1 := add_left_eq_self.mpr h1
  have h3 : ∀ x y, g (x + y) = g x + g y := λ x y ↦ by
    rw [add_add_add_comm, ← add_assoc, ← h0]
  have h4 : ∀ x y, g (x * y) = g x * g y := λ x y ↦ by
    rw [add_one_mul (f x), mul_add_one (f x), add_assoc, ← add_assoc (f x),
      ← h0, ← h, sub_add_cancel, h0, add_assoc, h1, zero_add]
  ⟨RingHom.mk' ⟨⟨g, h2⟩, h4⟩ h3, funext λ x ↦ (add_sub_cancel (f x) 1).symm⟩

/-- Corollary of the previous result -/
theorem IsAnswer_of_add_one_additive (h0 : ∀ x y, f (x + y) = f x + f y + 1) :
    IsAnswer f := by
  rcases eq_hom_sub_one_of h h0 with ⟨φ, rfl⟩
  exact IsAnswer.hom_sub_one φ
