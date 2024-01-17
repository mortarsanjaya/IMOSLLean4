/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Defs

/-!
# IMO 2011 A6 (P3)

Let $R$ be a totally ordered commutative ring.
Let $f : R → R$ be a function such that, for any $x, y ∈ R$,
$$ f(x + y) ≤ y f(x) + f(f(x)). $$
Show that $f(x) = 0$ for any $x ∈ R$ such that $x ≤ 0$.
-/

namespace IMOSL
namespace IMO2011A6

/-- Final solution -/
theorem final_solution [LinearOrderedCommRing R]
    {f : R → R} (h : ∀ x y : R, f (x + y) ≤ y * f x + f (f x)) :
    ∀ x : R, x ≤ 0 → f x = 0 := by
  have h0 : ∀ t x : R, f (f t) - f (f x) ≤ (f t - x) * f x := λ t x ↦ by
    rw [sub_le_iff_le_add]
    apply (h _ _).trans_eq'
    rw [add_sub_cancel'_right]
  replace h0 : ∀ t x : R, 0 ≤ (f t - x) * f x + (f x - t) * f t := λ t x ↦ by
    rw [← sub_self (f (f t)), ← sub_add_sub_cancel _ (f (f x))]
    exact add_le_add (h0 t x) (h0 x t)
  replace h0 : ∀ x : R, x * f x ≤ 0 := λ x ↦ by
    have h1 := h0 x (f x + f x)
    rwa [sub_add_cancel', sub_mul, neg_mul, mul_comm,
      ← add_sub_assoc, neg_add_self, zero_sub, neg_nonneg] at h1
  have h1 : ∀ x : R, f x ≤ f (f x) := λ x ↦ by
    have h1 := h x 0
    rwa [add_zero, zero_mul, zero_add] at h1
  replace h1 : ∀ x : R, f x ≤ 0 := λ x ↦
    le_of_not_lt λ h2 ↦ (h0 (f x)).not_lt <| mul_pos h2 (h2.trans_le (h1 x))
  replace h0 : ∀ x : R, x < 0 → f x = 0 := λ x h2 ↦
    (h1 x).antisymm (nonneg_of_mul_nonpos_right (h0 x) h2)
  intros x h2
  rcases h2.lt_or_eq with h2 | rfl
  · exact h0 x h2
  · apply (h1 0).antisymm
    specialize h (-1) 0
    rwa [add_zero, zero_mul, zero_add, h0 _ neg_one_lt_zero] at h
