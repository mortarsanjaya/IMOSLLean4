/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# IMO 2011 A3

Let $R$ be a commutative ring where $2$ is not a zero divisor.
Find all functions $f, g : R → R$ such that for any $x, y ∈ R$,
$$ g(f(x + y)) = f(x) + (2x + y) g(y). $$

### Extra notes

A lot of the steps are implemented without assuming that $R$ is commutative.
Not only that, we have a complete solution without commutativity if
  we do not look into some structural decomposition of $R$.
However, the more we try to go deeper, the messier things get.
-/

namespace IMOSL
namespace IMO2011A3

def good [NonUnitalNonAssocSemiring R] (f g : R → R) :=
  ∀ x y, g (f (x + y)) = f x + (2 • x + y) * g y

theorem main_answer_is_good [NonUnitalCommRing R] (C : R) :
    good (λ x ↦ x * x + C) id := λ x y ↦ by
  rw [id, id, add_right_comm, add_left_inj, two_nsmul, mul_add,
    add_mul, mul_comm y, add_assoc, ← add_mul, add_assoc]

theorem zero_is_good [NonUnitalNonAssocSemiring R] : good (λ _ : R ↦ 0) (λ _ ↦ 0) :=
    λ _ _ ↦ ((zero_add _).trans (mul_zero _)).symm



lemma step1_1 [NonUnitalNonAssocRing R] {f g : R → R} (h : good f g) (x y) :
    (f x - x * g x) - (f y - y * g y) = 2 • (y * g x - x * g y) := by
  rw [nsmul_sub, sub_eq_sub_iff_add_eq_add, ← add_sub_right_comm, ← add_sub_assoc,
    sub_eq_sub_iff_add_eq_add, two_nsmul, ← add_mul, add_assoc, ← add_mul,
    ← two_nsmul, ← h, add_comm _ (f y), add_assoc, two_nsmul, ← add_mul,
    ← add_mul, ← two_nsmul, ← h, add_comm]

theorem step1 [NonAssocRing R] (hR : ∀ x y : R, 2 • x = 2 • y → x = y)
    {f g : R → R} (h : good f g) :
    ∃ A B C : R, (f = λ x ↦ x * (x * A) - x * B + C) ∧ (g = (· * A + B)) := by
  ---- First obtain the equation for `g`
  obtain ⟨A, h0⟩ : ∃ A, ∀ x, g x = x * A + g 0 := ⟨g 1 - g 0, λ x ↦ by
    have h0 : _ + _ = _ + _ := congrArg₂ _ (step1_1 h x 1) (step1_1 h 1 0)
    rw [sub_add_sub_cancel, step1_1 h, ← nsmul_add] at h0
    replace h0 := hR _ _ h0
    rwa [zero_mul, zero_sub, one_mul, zero_mul, one_mul, zero_sub, eq_add_neg_iff_add_eq,
      eq_sub_iff_add_eq', ← add_assoc, ← sub_eq_add_neg, ← mul_sub, eq_comm] at h0⟩
  ---- Now obtain the equation for `f`
  refine ⟨A, g 0, f 0, funext λ x ↦ ?_, funext h0⟩
  have h1 := step1_1 h x 0
  rwa [zero_mul, sub_zero, zero_mul, zero_sub, sub_eq_iff_eq_add,
    sub_eq_iff_eq_add', h0, mul_add, two_nsmul, add_assoc _ _ (f 0),
    add_add_add_comm, add_neg_cancel_left, ← sub_eq_add_neg] at h1

theorem step2 [Ring R] (hR : ∀ x y : R, 2 • x = 2 • y → x = y)
    {A B C : R} (h : good (λ x ↦ x * (x * A) - x * B + C) (λ x ↦ x * A + B)) :
    B = 0 ∧ A * A = A ∧ C * A = C := by
  ---- First plug `y = -2x`
  have h0 (x) : (x * (x * A) + x * B + C) * A + B = x * (x * A) - x * B + C := by
    specialize h x (-(2 • x)); simp only at h
    rwa [add_neg_cancel, zero_mul, add_zero, two_nsmul, neg_add,
      add_neg_cancel_comm_assoc, neg_mul x A, neg_mul_neg, neg_mul, sub_neg_eq_add] at h
  ---- Now plug `h0` at various values of `x`
  have h1 := h0 0; rw [zero_mul, zero_mul, zero_add, sub_zero, zero_add] at h1
  have h2 := h0 1; rw [one_mul, one_mul, one_mul, add_mul, add_assoc, h1, add_left_inj] at h2
  have h3 := h0 (-1); rw [neg_one_mul, neg_one_mul, neg_one_mul, neg_neg,
    ← sub_eq_add_neg, sub_neg_eq_add, add_mul, add_assoc, h1, add_left_inj] at h3
  ---- Simplify more
  replace h3 : _ - _ = _ - _ := congrArg₂ (· - ·) h2 h3
  rw [← sub_mul, add_sub_sub_cancel, add_mul, ← two_nsmul, ← sub_sub,
    sub_sub_cancel_left, sub_eq_add_neg, ← two_nsmul] at h3
  replace h3 := hR _ _ h3
  rw [add_mul, h3, sub_eq_add_neg, add_left_inj] at h2
  ---- The rest needs associativity assumption on `R`
  replace h0 : _ * A = _ * A := congrArg (· * A) h1
  rw [add_mul, mul_assoc, h2, add_eq_left, h3, neg_eq_zero] at h0
  rw [h0, add_zero] at h1; exact ⟨h0, h2, h1⟩

theorem relation_summary [Ring R] (hR : ∀ x y : R, 2 • x = 2 • y → x = y)
    {f g : R → R} (h : good f g) :
    ∃ A C : R, A * A = A ∧ C * A = C ∧ (f = λ x ↦ x * x * A + C) ∧ (g = (· * A)) := by
  rcases step1 hR h with ⟨A, B, C, rfl, rfl⟩
  rcases step2 hR h with ⟨rfl, h0, h1⟩
  refine ⟨A, C, h0, h1, ?_, ?_⟩
  · funext x; rw [mul_zero, sub_zero, ← mul_assoc]
  · exact funext λ x ↦ add_zero (x * A)





/-- Final solution -/
theorem final_solution [CommRing R] [IsDomain R] (hR : (2 : R) ≠ 0) {f g : R → R} :
    good f g ↔ (f, g) = (λ _ ↦ 0, λ _ ↦ 0) ∨ ∃ c, (f, g) = (λ x ↦ x * x + c, id) := by
  refine ⟨?_, ?_⟩
  · intro h; replace hR (x y : R) (h0 : 2 • x = 2 • y) : x = y :=
      mul_left_cancel₀ hR (by simpa only [two_mul, ← two_nsmul])
    obtain ⟨A, C, h0, h1, rfl, rfl⟩ := relation_summary hR h
    replace h0 : A = 0 ∨ A = 1 :=
      (eq_or_ne A 0).imp_right λ h2 ↦ mul_left_cancel₀ h2 (h0.trans (mul_one A).symm)
    revert h0; apply Or.imp
    · rintro rfl; simp only [mul_zero, zero_add]
      rw [mul_zero] at h1; subst h1; rfl
    · rintro rfl; simp only [mul_one]
      exact ⟨C, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨c, rfl, rfl⟩)
    exacts [zero_is_good, main_answer_is_good c]
