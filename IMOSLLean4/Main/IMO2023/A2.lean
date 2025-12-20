/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Defs

/-!
# IMO 2023 A2

Let $G$ be an abelian group and $R$ be a totally ordered ring.
Suppose that $G$ is *$2$-divisible*: for every $x ∈ G$, there exists $y ∈ G$ with $2y = x$.
Let $f, g : G → R$ be a function such that
* $f(x + y) f(x - y) ≥ g(x) - g(y)$ for all $x, y ∈ G$,
* $f(x_0 + y_0) f(x_0 - y_0) > g(x_0) - g(y_0)$ for some $x_0, y_0 ∈ G$.

Prove that either $f ≥ 0$ or $f ≤ 0$.

(In the original formulation, $g(x) = f(x)^2$.)

### Solution

We follow Solution 1 of the
  [official solution](http://www.imo-official.org/problems/IMO2023SL.pdf).
The main idea is just looking at the inequality
$$ f(x + y) (f(x - y) + f(y - x)) ≥ (g(x) - g(y)) + (g(y) - g(x)) = 0. $$
-/

namespace IMOSL
namespace IMO2023A2

/-- Final solution -/
theorem final_solution [AddCommGroup G] (hG : ∀ x : G, ∃ y, 2 • y = x)
    [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {f g : G → R}
    (hf : ∀ x y, g x - g y ≤ f (x + y) * f (x - y))
    (hf0 : ∃ x₀ y₀, g x₀ - g y₀ < f (x₀ + y₀) * f (x₀ - y₀)) :
    (∀ x, 0 ≤ f x) ∨ (∀ x, f x ≤ 0) := by
  ---- First, the given condition implies `f(t) + f(-t) ≠ 0`, where `t = x₀ - y₀`.
  obtain ⟨t, ht⟩ : ∃ t, f t + f (-t) ≠ 0 := by
    rcases hf0 with ⟨x₀, y₀, h⟩
    refine ⟨x₀ - y₀, right_ne_zero_of_mul (a := f (x₀ + y₀)) (ne_of_gt ?_)⟩
    simpa only [neg_sub, mul_add, sub_add_sub_cancel, sub_self, add_comm y₀]
      using add_lt_add_of_lt_of_le h (hf y₀ x₀)
  ---- Now by the same calculation, we get `f(s) (f(t) + f(-t)) ≥ 0` for all `s ∈ G`.
  replace hf (s) : 0 ≤ f s * (f t + f (-t)) := by
    -- Before that, we need to write `s = x + y` and `t = x - y` for some `x, y ∈ G`.
    obtain ⟨x, y, rfl, rfl⟩ : ∃ x y, s = x + y ∧ t = x - y := by
      obtain ⟨v, rfl⟩ : ∃ v, 2 • v = s := hG s
      obtain ⟨w, rfl⟩ : ∃ w, 2 • w = t := hG t
      refine ⟨v + w, v - w, ?_, ?_⟩
      · rw [add_add_sub_cancel, two_nsmul]
      · rw [add_sub_sub_cancel, two_nsmul]
    -- Now redo the calculation
    simpa only [neg_sub, mul_add, sub_add_sub_cancel, sub_self, add_comm y]
      using add_le_add (hf x y) (hf y x)
  ---- Finish by splitting the sign case for `f(t) + f(-t)`.
  exact ht.symm.lt_or_gt.imp
    (λ h x ↦ nonneg_of_mul_nonneg_left (hf x) h)
    (λ h x ↦ nonpos_of_mul_nonneg_left (hf x) h)
