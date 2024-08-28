/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic

/-!
# IMO 2021 A8 (Definitions)

Let $F$ be a field and $S$ be a domain.
Find all functions $f : F → S$ such that for any $a, b, c ∈ F$,
$$ (f(a) - f(b))(f(b) - f(c))(f(c) - f(a)) = f(ab^2 + bc^2 + ca^2) - f(ba^2 + ac^2 + cb^2). $$

...
-/

namespace IMOSL
namespace IMO2021A8

variable [Semiring R] [NonAssocRing S]

/-- The main problem. -/
def good (f : R → S) :=
  ∀ a b c : R, (f a - f b) * (f b - f c) * (f c - f a)
    = f (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) - f (b * a ^ 2 + c * b ^ 2 + a * c ^ 2)

theorem const_is_good (s : S) : good (λ _ : R ↦ s) := λ _ _ _ ↦ by
  simp only [sub_self, mul_zero]

theorem good.add_const {f : R → S} (hf : good f) (s : S) : good (λ x ↦ f x + s) := by
  simpa only [good, add_sub_add_right_eq_sub]

theorem good.sub_const {f : R → S} (hf : good f) (s : S) : good (λ x ↦ f x - s) := by
  simpa only [good, sub_sub_sub_cancel_right]

theorem good.neg {f : R → S} (hf : good f) : good (λ x ↦ -f x) := λ a b c ↦ by
  simp only [← neg_sub']; rw [neg_mul_neg, mul_neg, neg_inj, hf]


/-- Normalized good function. -/
structure NormalizedGood (f : R → S) : Prop where
  is_good : good f
  map_zero : f 0 = 0

theorem good.Normalized_sub_map_zero {f : R → S} (hf : good f) :
    NormalizedGood (λ x ↦ f x - f 0) where
  is_good := hf.sub_const (f 0)
  map_zero := sub_self (f 0)

theorem zero_is_NormalizedGood : NormalizedGood (λ _ : R ↦ (0 : S)) where
  is_good := const_is_good 0
  map_zero := rfl
