/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Lemmas.Hom
import IMOSLLean4.IMO2017.A6.A6Lemmas.Period
import IMOSLLean4.IMO2017.A6.A6Lemmas.ReducedNZD2
import Mathlib.Algebra.Group.Invertible.Defs

/-!
# IMO 2017 A6 (P2, General solution)

The general solution to the functional equation can be described as follows.
Let `φ : R → S` be a homomorphism of rings.
Suppose that `φ` has a right inverse `ι : S → R` that is a group homomorphism.
Then the function `x ↦ ι(a(1 - φ(x)))` is good for any `a ∈ Z(S)` with `a^2 = 1`.
The main goal is to prove that these consitutes all good functions (over `R`).

This file proves that this is true in some special cases of `R`.
Currently, we prove it when `2 ∈ Rˣ` and `3 ∈ R⁰`.
Here, `R⁰` is the set of non-zero divisors of `R`.
-/

namespace IMOSL
namespace IMO2017A6

open scoped nonZeroDivisors

variable {R : Type u} [Ring R] [Invertible (2 : R)]

/-! ### Results on the quotient map by period -/

namespace good

variable {f : R → R} (hf : good f)

private local instance : Invertible (2 : hf.toRingCon.Quotient) :=
  ⟨(⅟2 : R), congrArg _ (invOf_mul_self _), congrArg _ (mul_invOf_self _)⟩

private lemma toQuotient_NZD2 : 2 ∈ hf.toRingCon.Quotient⁰ := λ x h ↦ by
  rw [← mul_mul_invOf_self_cancel x 2, h, zero_mul]

lemma InvertibleTwo_quotient_map_zero_mul_self : (f 0 : hf.toRingCon.Quotient) * f 0 = 1 :=
  hf.toQuotientMap_ReducedGood.NZD2_map_zero_mul_self hf.toQuotient_NZD2

lemma InvertibleTwo_quotient_eq (x) : (f x : hf.toRingCon.Quotient) = f 0 * (1 - x) :=
  hf.toQuotientMap_ReducedGood.NZD2_solution hf.toQuotient_NZD2 x

lemma InvertibleTwo_quotient_map_zero_comm (x) :
    (f 0 : hf.toRingCon.Quotient) * x = x * f 0 :=
  hf.toQuotientMap_ReducedGood.NZD2_map_zero_comm hf.toQuotient_NZD2 x

lemma InvertibleTwo_altFE' (x y : R) : f ((1 - x) * (1 - y)) + f (x + y) = f (x * y) := by
  rw [← hf x, add_left_inj]
  apply hf.apply_eq_of_toRingQuot_eq
  have h := hf.InvertibleTwo_quotient_eq
  rw [RingCon.coe_mul, RingCon.coe_mul, h, h y, hf.InvertibleTwo_quotient_map_zero_comm,
    mul_assoc, ← mul_assoc (f 0 : hf.toRingCon.Quotient), RingCon.coe_sub, RingCon.coe_sub,
    hf.InvertibleTwo_quotient_map_zero_mul_self, one_mul, RingCon.coe_one]

lemma InvertibleTwo_altFE :
    ∀ x y, hf.toPartialQuotientMap ((1 - x) * (1 - y))
      + hf.toPartialQuotientMap (x + y) = hf.toPartialQuotientMap (x * y) :=
  Quotient.ind₂ hf.InvertibleTwo_altFE'

end good





/-! ### Solution to the alternative functional equation -/

theorem altFE_solution [AddCommGroup G]
    (hG2 : ∀ x y : G, 2 • x = 2 • y → x = y) (hG3 : ∀ x y : G, 3 • x = 3 • y → x = y)
    {f : R → G} (h : ∀ x y, f ((1 - x) * (1 - y)) + f (x + y) = f (x * y)) :
    ∃ φ : R →+ G, φ = λ x ↦ f (1 - x) := by
  ---- First change the FE to an FE for `g(x) = f(1 - x)`
  set g : R → G := λ x ↦ f (1 - x)
  refine ⟨AddMonoidHom.mk' g ?_, rfl⟩
  replace h (x y) : g (x + y - x * y) + g (1 - (x + y)) = g (1 - x * y) := by
    dsimp only [g]; rw [sub_sub_cancel, sub_sub_cancel, ← h,
      add_sub_assoc, ← one_sub_mul, ← sub_sub, ← mul_one_sub]
  clear_value g; clear f
  ---- Now just prove more and more properties
  have hG2 := hG2
  have hG3 := hG3
  /-
  have h0 (x) : g (x + 1) = g x + g 1 := by
    dsimp only [g]; rw [sub_add_cancel_right, sub_self, sub_eq_add_neg]
    specialize h 1 (-x); rwa [sub_self, zero_mul, one_mul, add_comm, eq_comm] at h
  have h1 (x) : g (-x) = -g x := by
    specialize h 0 x; rw [sub_zero, one_mul, zero_add, zero_mul, ← sub_self 1] at h
    change g x + f x = g 1 at h; rw [eq_sub_of_add_eq h, neg_sub, eq_sub_iff_add_eq, ← h0]
    dsimp only [g]; rw [sub_add_cancel_right, neg_neg]
  replace h (x y) : g (x * y - (x + y)) + g (x + y) = g (x * y)
  -/
  sorry





/-! ### Final solution -/

open Function

theorem general_good_iff (hR : 3 ∈ R⁰) {f : R → R} :
    good f ↔ ∃ (S : Type u) (_ : Ring S) (φ : R →+* S) (ι : S →+ R) (h : LeftInverse φ ι)
      (a : S) (_ : a * a = 1) (_ : ∀ x, a * x = x * a), f = λ x ↦ ι (a * (1 - φ x)) :=
  ⟨λ hf ↦ by
    obtain ⟨ι, h0⟩ : ∃ ι : hf.toRingCon.Quotient →+ R,
        ι = λ x ↦ hf.toPartialQuotientMap (1 - x) := by
      refine altFE_solution ?_ ?_ hf.InvertibleTwo_altFE
      · intro x y h; rw [two_nsmul, ← two_mul, two_nsmul, ← two_mul] at h
        exact (mul_left_inj_of_invertible 2).mp h
      · intro x y h; rw [nsmul_eq_mul', nsmul_eq_mul', Nat.cast_ofNat] at h
        exact (mul_cancel_right_mem_nonZeroDivisors hR).mp h
    have h1 := hf.InvertibleTwo_quotient_map_zero_mul_self
    refine ⟨hf.toRingCon.Quotient, hf.toRingCon.instRingQuotient,
      hf.toRingCon.mk', ι.comp (AddMonoidHom.mulLeft (f 0)), ?_, f 0,
      h1, hf.InvertibleTwo_quotient_map_zero_comm, funext λ x ↦ ?_⟩
    · refine Quotient.ind λ x ↦ ?_
      rw [AddMonoidHom.coe_comp, comp_apply, h0]
      change (f (1 - f 0 * x)) = (x : hf.toRingCon.Quotient)
      rw [hf.InvertibleTwo_quotient_eq, RingCon.coe_sub, RingCon.coe_one,
        sub_sub_cancel, RingCon.coe_mul, ← mul_assoc, h1, one_mul]
    · rw [AddMonoidHom.coe_comp, comp_apply, h0]
      change f x = hf.toPartialQuotientMap (1 - f 0 * _)
      rw [← mul_assoc, h1, one_mul, sub_sub_cancel]; rfl,
  λ ⟨S, _, φ, ι, h, a, ha, ha0, hf⟩ ↦
    hf ▸ good.to_hom_pair φ ι h (mul_one_sub_is_good ha ha0)⟩
