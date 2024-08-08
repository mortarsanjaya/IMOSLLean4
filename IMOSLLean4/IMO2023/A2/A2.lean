/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Defs

/-!
# IMO 2023 A2

Let $G$ be a $2$-divisible abelian group and $R$ be a totally ordered ring.
Let $f : G → R$ be a function such that
* $f(x + y) f(x - y) ≥ f(x)^2 - f(y)^2$ for all $x, y ∈ G$,
* $f(x_0 + y_0) f(x_0 - y_0) > f(x_0)^2 - f(y_0)^2$ for some $x_0, y_0 ∈ G$.

Prove that either $f ≥ 0$ or $f ≤ 0$.
-/

namespace IMOSL
namespace IMO2023A2

/-- Final solution -/
theorem final_solution [AddCommGroup G] (hG : ∀ x : G, ∃ y, 2 • y = x) [LinearOrderedRing R]
    {f : G → R} (hf : ∀ x y, f x ^ 2 - f y ^ 2 ≤ f (x + y) * f (x - y))
    (hf0 : ∃ x0 y0, f x0 ^ 2 - f y0 ^ 2 < f (x0 + y0) * f (x0 - y0)) :
    (∀ x, 0 ≤ f x) ∨ (∀ x, f x ≤ 0) := by
  replace hf0 : ∃ s, f s + f (-s) ≠ 0 := by
    rcases hf0 with ⟨x0, y0, hf0⟩
    refine ⟨x0 - y0, λ h ↦ (add_lt_add_of_lt_of_le hf0 (hf y0 x0)).ne ?_⟩
    rw [sub_add_sub_cancel, sub_self, add_comm x0, ← mul_add, ← neg_sub x0, h, mul_zero]
  replace hf (x y) : 0 ≤ f (x + y) * (f (x - y) + f (-(x - y))) := by
    have h := add_le_add (hf x y) (hf y x)
    rwa [sub_add_sub_cancel, sub_self, add_comm y, ← neg_sub x, ← mul_add] at h
  replace hf (s t) : 0 ≤ f t * (f s + f (-s)) := by
    obtain ⟨v, rfl⟩ := hG t
    obtain ⟨w, rfl⟩ := hG s
    specialize hf (v + w) (v - w)
    rwa [add_add_sub_cancel, add_sub_sub_cancel, ← two_nsmul, ← two_nsmul] at hf
  ---- Now finish
  rcases hf0 with ⟨s, hf0⟩; rw [ne_iff_lt_or_gt, or_comm] at hf0
  revert hf0; exact Or.imp (λ h x ↦ nonneg_of_mul_nonneg_left (hf s x) h)
    (λ h x ↦ nonpos_of_mul_nonneg_left (hf s x) h)
