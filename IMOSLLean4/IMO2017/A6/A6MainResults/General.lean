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

/-! ### Results on the quotient map by period -/

namespace good

variable [Ring R] [Invertible (2 : R)] {f : R → R} (hf : good f)
include hf

private local instance : Invertible (2 : hf.toRingCon.Quotient) :=
  ⟨(⅟2 : R), congrArg _ (invOf_mul_self _), congrArg _ (mul_invOf_self _)⟩

private lemma toQuotient_NZD2 : 2 ∈ hf.toRingCon.Quotient⁰ := λ x h ↦ by
  rw [← mul_invOf_cancel_right x 2, h, zero_mul]

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

theorem altFE_solution [Ring R] [AddCommGroup G]
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
  have h0' (x) : g (x + 1) = g x + g 1 := by
    specialize h (-x) 1; rwa [mul_one, sub_neg_eq_add, neg_add_cancel_comm,
      sub_add_cancel_right, neg_neg, sub_neg_eq_add, add_comm, add_comm 1, eq_comm] at h
  have h0 (x : R) : ∀ n : ℕ, g (x + n) = g x + n • g 1 :=
    Nat.rec (by rw [Nat.cast_zero, add_zero, zero_nsmul, add_zero])
      λ n hn ↦ by rw [Nat.cast_succ, ← add_assoc, h0', hn, add_assoc, succ_nsmul]
  have h1 (x) : g (-x) = -g x := by
    specialize h 0 x; rwa [zero_add, zero_mul, sub_zero, sub_zero, sub_eq_add_neg,
      ← eq_neg_add_iff_add_eq, add_comm 1, h0', add_left_inj] at h
  replace h (x y) : g (x * y + (x + y)) = g (x * y) + g (x + y) := by
    specialize h (-x) (-y)
    rwa [neg_mul_neg, ← neg_add, ← neg_add', h1, sub_neg_eq_add, add_comm 1,
      h0', sub_eq_add_neg, add_comm 1, h0', ← add_assoc, add_left_inj,
      h1, ← eq_sub_iff_add_eq, ← neg_add', neg_inj, add_comm] at h
  have h₁ (x y) : g ((x + 1) * (y + 1)) = g (x * y) + g (x + y) + g 1 := by
    rw [add_one_mul x, mul_add_one x, ← add_assoc, h0', add_assoc, h]
  replace h : ∀ (n : ℕ) (x y : R),
      g ((x + n) * (y + n)) = g (x * y) + n • g (x + y) + n ^ 2 • g 1 := by
    refine Nat.rec (λ x y ↦ ?_) (λ n hn x y ↦ ?_)
    · rw [Nat.cast_zero, add_zero, add_zero, zero_nsmul,
        sq, add_zero, Nat.zero_mul, zero_nsmul, add_zero]
    · rw [Nat.cast_succ, ← add_assoc, ← add_assoc, h₁, add_add_add_comm, ← Nat.cast_add,
        h0, ← add_assoc, add_assoc, ← succ_nsmul, hn, add_right_comm _ _ (g _),
        add_assoc _ (_ • g 1), ← add_nsmul, add_assoc (g _), ← succ_nsmul, sq,
        n.add_assoc, ← (n * n).add_assoc, sq, ← n.succ_mul, ← n.succ.mul_succ]
  replace h1 (n : ℕ) (x : R) : g (n * x) = n • g x := by
    have h2 : g 0 = 0 := by rw [← add_left_inj, ← h0', zero_add, zero_add]
    specialize h n 0 x; rwa [zero_add, mul_add, ← Nat.cast_mul,
      h0, zero_mul, h2, zero_add, zero_add, sq, add_left_inj] at h
  replace h₁ : ∀ x y, g ((x + 2) * (y + 2)) = g (x * y) + 2 • g (x + y) + 4 • g 1 := h 2
  replace h0' (x y) : g ((x + 1) * (y + 2)) = g (x * y) + g (2 * x + y) + 2 • g 1 := by
    specialize h₁ (2 * x) y
    rw [← mul_add_one (2 : R), mul_assoc, mul_assoc, ← Nat.cast_two,
      h1, h1, mul_nsmul _ 2 2, ← nsmul_add, ← nsmul_add] at h₁
    exact hG2 _ _ h₁
  replace h₁ (x y) : g ((x + 2) * (y + 1)) = g (x * y) + g (x + y * 2) + 2 • g 1 := by
    have X (x : R) : 2 * x = x * 2 := by rw [two_mul, mul_two]
    specialize h₁ x (y * 2)
    rw [← add_one_mul y, ← mul_assoc, ← X, ← mul_assoc x, ← X, ← Nat.cast_two,
      h1, h1, mul_nsmul _ 2 2, ← nsmul_add, ← nsmul_add] at h₁
    exact hG2 _ _ h₁
  replace h (x y) : g (2 * x + y) + g (x + y * 2) = 3 • g (x + y) := by
    specialize h0' (x + 2) (y + 1)
    rw [add_assoc, add_assoc, add_comm 1, two_add_one_eq_three] at h0'
    have X : ((3 : ℕ) : R) = 3 := rfl
    rw [← X, h, h₁, add_assoc, add_assoc, add_add_add_comm, add_assoc (g _),
      add_assoc, add_right_inj, mul_add, ← add_nsmul, add_add_add_comm] at h0'
    replace X : 2 * 2 + 1 = ((5 : ℕ) : R) := by
      rw [Nat.cast_succ, Nat.cast_mul 2 2, Nat.cast_two]
    rw [X, h0, add_assoc, add_assoc, ← add_nsmul, add_left_comm, ← add_assoc] at h0'
    exact (add_left_injective _ h0').symm
  clear h0' h0 h₁
  ---- Now the finishing argument
  intro a b
  specialize h (a + (a - b)) (b - (a - b))
  have X (x : R) : (3 : ℕ) * x = x + (x + x) := by
    rw [Nat.cast_succ, Nat.cast_two, add_one_mul 2 x, two_mul, add_comm]
  rw [two_mul, mul_two, add_left_comm (a + (a - b)) (b - _), add_assoc,
    add_add_sub_cancel, add_assoc, sub_add_add_cancel, ← X, h1, sub_add, sub_sub,
    add_left_comm b a, sub_add_cancel_left, sub_neg_eq_add, ← X, h1, ← nsmul_add] at h
  exact (hG3 _ _ h).symm





/-! ### Final solution -/

open Function

theorem general_good_iff {R : Type u} [Ring R] [Invertible (2 : R)] (hR : 3 ∈ R⁰) {f : R → R} :
    good f ↔ ∃ (S : Type u) (_ : Ring S) (φ : R →+* S) (ι : S →+ R) (_ : LeftInverse φ ι)
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
