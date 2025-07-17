/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# IMO 2016 A4

Let $M$ be an integral multiplicative monoid with a cancellative, distributive addition.
Find all functions $f : M → M$ such that, for all $x, y ∈ M$,
$$ x f(x^2) f(f(y)) + f(y f(x)) = f(xy) \left(f(f(y^2)) + f(f(x^2))\right). $$
-/

namespace IMOSL
namespace IMO2016A4

def good [Mul M] [Add M] (f : M → M) :=
  ∀ x y, x * f (x * x) * f (f y) + f (y * f x) = f (x * y) * (f (f (y * y)) + f (f (x * x)))

class CancelCommDistribMonoid (M) extends CancelCommMonoid M, Distrib M

variable [CancelCommDistribMonoid M]

lemma inv'_is_good {f : M → M} (h : ∀ x, x * f x = 1) : good f := λ x y ↦ by
  have h0 (y) : f (f y) = y := by rw [← mul_left_cancel_iff, h, mul_comm, h]
  rw [h0, h0, h0, mul_add]; apply congrArg₂
  · rw [← mul_assoc, ← mul_left_cancel_iff (a := x), ← mul_assoc,
      ← mul_assoc, h, ← mul_assoc, mul_comm (f _), ← mul_assoc, h]
  · rw [← mul_left_cancel_iff (a := y * f x), h, mul_comm,
      mul_assoc, mul_mul_mul_comm, h, mul_one, mul_comm, h]

theorem good_imp_inv' [IsCancelAdd M] {f : M → M} (hf : good f) : ∀ x, x * f x = 1 := by
  have h : f 1 = 1 := by simpa [mul_add] using hf 1 1
  have h0 (y) : f y * f (f (y * y)) = f (f y) := by simpa [h, mul_add] using (hf 1 y).symm
  replace h (x) : x * f (x * x) = f x := by simpa [h0, mul_add] using hf x 1
  replace h0 (x) : f (f (x * x)) = f (f x * f x) := by rw [← mul_right_inj, h0, h]
  suffices f.Injective from λ x ↦ by
    rw [← mul_eq_right (b := f x), mul_assoc, ← this (h0 x), h]
  replace hf (x y) : f x * f (f y) + f (y * f x)
      = f (x * y) * (f (f y * f y) + f (f x * f x)) := by
    specialize hf x y; rwa [h, h0, h0] at hf
  replace hf {a b} (h1 : f a = f b) (y) : f (a * y) = f (b * y) := by
    have h2 := (hf a y).symm; rwa [h1, hf, mul_left_inj] at h2
  intro a b h1
  have h2 : f (a * a) = f (b * b) := by rw [hf h1, mul_comm, hf h1]
  rw [← mul_left_inj, h, h2, h, h1]

/-- Final solution -/
theorem final_solution [IsCancelAdd M] {f : M → M} : good f ↔ ∀ x, x * f x = 1 :=
  ⟨good_imp_inv', inv'_is_good⟩
