/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Real.CompleteField

/-!
# IMO 2012 A5

Let $S$ be an integral domain.
Find all functions $f : ℝ → S$ such that $f(-1) ≠ 0$ and for any $x, y ∈ ℝ$,
$$ f(xy + 1) = f(x) f(y) + f(x + y). $$

### Answer

$f(x) = φ(x) - 1$ for some ring homomorphism $φ : ℝ → S$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf).
We skip (4) and immediately prove that the function $g(x) = f(x) + 1$ is odd.
The method essentially follows from the official solution as well.

The same method works even with the generalized codomain.
Note that the only ring homomorphism from $ℝ$ to itself is the identity map.
However, we have to add a step of showing that $S$ cannot have characteristic $2$.
This is done when obtaining $g(1 + xy) = 1 + g(x) g(y)$, where again $g(x) = f(x) + 1$.

### Generalization

Several AoPS users have also solved the problem without the assumption $f(-1) ≠ 0$.
See [this thread](https://artofproblemsolving.com/community/c6h546165p3160554).
In particular, the only extra functions are $f ≡ 0$ and $f(x) = x^2 - 1$.

It is even possible to find all functions $f : R → S$ satisfying the functional equation,
  where $R$ is a ring and $S$ is a domain; no commutativity is assumed.
See `IMOSLLean4/Generalization/IMO2012A5/IMO2012A5.lean` for the implementation.
-/

namespace IMOSL
namespace IMO2012A5

/-- A function `f : R → S` is called *good* if
  `f(xy + 1) = f(x) f(y) + f(x + y)` for all `x, y ∈ R`. -/
def good [Semiring R] [Semiring S] (f : R → S) :=
  ∀ x y : R, f (x * y + 1) = f x * f y + f (x + y)


section

variable [Semiring R] [Ring S]

/-- A function `g : R → S` is called *good'* if
  `g(xy + 1) = (g(x) - 1)(g(y) - 1) + g(x + y)` for all `x, y ∈ R`. -/
def good' (g : R → S) :=
  ∀ x y : R, g (x * y + 1) = (g x - 1) * (g y - 1) + g (x + y)

/-- `f` is good if and only if `f + 1` is good'. -/
theorem good_iff_good' {f : R → S} : good f ↔ good' (f · + 1) := by
  refine forall₂_congr λ x y ↦ ?_
  rw [add_sub_cancel_right, add_sub_cancel_right, ← add_assoc, add_left_inj]

/-- A ring homomorphism is always good'. -/
theorem RingHom_is_good' (φ : R →+* S) : good' φ := by
  intro x y; rw [φ.map_add, φ.map_one, φ.map_mul, sub_one_mul, mul_sub_one, sub_sub,
    ← add_sub_assoc, ← sub_add, φ.map_add, add_right_comm, sub_add_cancel]

end


namespace good'

/-- If `g : R → S` is good', then `g(1 - x) = (g(-1) - 1)(g(x) - 1) + g(x - 1)`. -/
theorem eq2_map_one_sub [Ring R] [Ring S] {g : R → S} (hg : good' g) (x) :
    g (1 - x) = (g (-1) - 1) * (g x - 1) + g (x - 1) :=
  calc g (1 - x)
  _ = g (-1 * x + 1) := by rw [neg_one_mul, sub_eq_neg_add]
  _ = (g (-1) - 1) * (g x - 1) + g (-1 + x) := hg (-1) x
  _ = (g (-1) - 1) * (g x - 1) + g (x - 1) := by rw [neg_add_eq_sub]


section

variable [Ring R] [Ring S] [IsDomain S] {g : R → S} (hg : good' g) (hg0 : g (-1) ≠ 1)
include hg hg0

/-- If `g : R → S` is good' and `g(-1) ≠ 1`, then `g(1) = 1`. -/
theorem map_one_eq_one : g 1 = 1 := by
  have h := hg.eq2_map_one_sub 1
  rw [sub_self, right_eq_add, mul_eq_zero, sub_eq_zero, sub_eq_zero] at h
  exact h.resolve_left hg0

/-- If `g : R → S` is good' and `g(-1) ≠ 1`, then `g(0) = 0`. -/
theorem map_zero_eq_zero : g 0 = 0 := by
  have h := hg.eq2_map_one_sub 0
  rw [sub_zero, zero_sub, hg.map_one_eq_one hg0, eq_comm, mul_sub_one, sub_add,
    sub_sub_cancel_left, sub_neg_eq_add, add_eq_right, mul_eq_zero, sub_eq_zero] at h
  exact h.resolve_left hg0

/-- If `g : R → S` is good', then `g(1 + x) + g(1 - x) = 2` for all `x`. -/
theorem eq3_map_one_add_add_map_one_sub (x) : g (1 + x) + g (1 - x) = 2 := by
  ---- One step is getting `g(-x) = (g(-1) - 1)(g(1 + x) - 1)` for all `x`.
  have hg1 (x) : g (-x) = (g (-1) - 1) * (g (1 + x) - 1) + g x := by
    simpa only [sub_add_cancel_left, add_sub_cancel_left] using hg.eq2_map_one_sub (1 + x)
  ---- The rest should be straightforward.
  replace hg1 : (g (-1) - 1) * (g (1 + x) - 1 + (g (1 - x) - 1)) = 0 := by
    rw [mul_add, ← sub_eq_of_eq_add (hg1 x), sub_eq_add_neg 1 x,
      ← sub_eq_of_eq_add (hg1 (-x)), neg_neg, sub_add_sub_cancel, sub_self]
  rwa [mul_eq_zero, sub_eq_zero, or_iff_right hg0,
    ← add_sub_add_comm, sub_eq_zero, one_add_one_eq_two] at hg1

end


section

variable [Ring S] [IsDomain S] {g : ℝ → S} (hg : good' g) (hg0 : g (-1) ≠ 1)
include hg hg0

/-- If `g : ℝ → S` is good' and `g(-1) ≠ 1`, then `g` is odd. -/
theorem Real_odd (x) : g (-x) = -g x := by
  ---- Recall that `g(1 + t) + g(1 - t) = 2` for all `t ∈ ℝ`.
  have hg1 (t) : g (1 + t) + g (1 - t) = 2 := hg.eq3_map_one_add_add_map_one_sub hg0 t
  ---- First show that `g(u(1 - u) + 3) - g(u(1 - u) + 1)` is constant with respect to `u`.
  obtain ⟨c, h⟩ : ∃ c, ∀ u, g (u * (1 - u) + 1 + 2) - g (u * (1 - u) + 1) = c := by
    refine ⟨g 3 - g 1, λ u ↦ sub_eq_sub_iff_sub_eq_sub.mp ?_⟩
    calc g (u * (1 - u) + 1 + 2) - g 3
      _ = g ((1 + (1 - u)) * (1 + u) + 1) - g ((1 + (1 - u)) + (1 + u)) :=
        congrArg₂ (g · - g ·) (by ring) (by ring)
      _ = (g (1 + (1 - u)) - 1) * (g (1 + u) - 1) := sub_eq_of_eq_add (hg _ _)
      _ = (2 - g (1 - (1 - u)) - 1) * (2 - g (1 - u) - 1) := by
        iterate 2 rw [eq_sub_of_add_eq (hg1 _)]
      _ = (g u - 1) * (g (1 - u) - 1) := by
        have h (a : S) : 2 - a - 1 = -(a - 1) := by
          rw [← one_add_one_eq_two, sub_sub, add_sub_add_right_eq_sub, neg_sub]
        rw [sub_sub_cancel, h, h, neg_mul_neg]
      _ = g (u * (1 - u) + 1) - g 1 := by
        rw [hg, add_sub_cancel, add_sub_cancel_right]
  ---- By the property of `ℝ`, `g(t + 2) - g(t)` is constant across all `t ≤ 0`.
  replace h (t : ℝ) (ht : t ≤ 0) : g (t + 2) - g t = c := by
    -- This holds via `u(1 - u) + 1 = t` for `u = 1/2 + sqrt(5/4 - t)`.
    suffices ht : ∃ u, u * (1 - u) + 1 = t
      by rcases ht with ⟨u, rfl⟩; exact h u
    refine ⟨2⁻¹ + √(5 / 4 - t), ?_⟩
    replace ht : 0 ≤ 5 / 4 - t := sub_nonneg_of_le (ht.trans (by norm_num))
    ring_nf; rw [Real.sq_sqrt ht, sub_sub_cancel]
  ---- The constant is `2` since `g(0) = 0` and `g(2) = 2`.
  obtain rfl : c = 2 := by
    have h0 : g 0 = 0 := hg.map_zero_eq_zero hg0
    have h1 : g 2 = 2 := calc
      _ = g (1 + 1) + g (1 - 1) := by rw [one_add_one_eq_two, sub_self, h0, add_zero]
      _ = 2 := hg1 1
    rw [← h 0 (le_refl 0), zero_add, h1, h0, sub_zero]
  ---- Now WLOG assume `x ≤ 0`.
  wlog hx : x ≤ 0 generalizing x
  · replace hx : -x ≤ 0 := Right.neg_nonpos_iff.mpr (le_of_not_ge hx)
    rw [← neg_eq_iff_eq_neg, ← this _ hx, neg_neg]
  ---- We are done by `g(x + 2) - g(x) = 2 = g(1 + (1 + x)) + g(1 - (1 + x))`.
  calc g (-x)
    _ = g (1 - (1 + x)) := by rw [sub_add_cancel_left]
    _ = 2 - g (1 + (1 + x)) := by rw [← hg1 (1 + x), add_sub_cancel_left]
    _ = g (x + 2) - g x - g (2 + x) := by rw [h x hx, ← add_assoc, one_add_one_eq_two]
    _ = -g x := by rw [add_comm, sub_sub_cancel_left]

/-- If `g : ℝ → S` is good' and `g(-1) ≠ 1`, then `g` is a ring homomorphism. -/
theorem Real_is_hom : ∃ φ : ℝ →+* S, g = φ := by
  have h : g 1 = 1 := hg.map_one_eq_one hg0
  have h0 (x) : g (-x) = -g x := hg.Real_odd hg0 x
  ---- First show that `char(S) ≠ 2` (e.g. follows from `1 ≠ g(-1) = -g(1) = -1`.)
  replace hg0 : (2 : S) ≠ 0 := by
    rwa [h0, h, Ne, neg_eq_iff_add_eq_zero, one_add_one_eq_two] at hg0
  ---- Derive the formula `g (xy + 1) = g(x) g(y) + 1 + g(x + y) - (g(x) + g(y))`.
  have h1 (x y) : g (x * y + 1) = g x * g y + 1 + (g (x + y) - (g x + g y)) := by
    rw [hg, sub_one_mul, mul_sub_one, ← sub_add,
      sub_sub, ← add_sub_right_comm, ← add_comm_sub]
  ---- Now use the above formula to show that `g` is additive.
  replace h0 (x y) : g (x + y) = g x + g y := by
    -- Compare the previous formula using `(-x, -y)` vs using `(x, y)`.
    have h2 := h1 (-x) (-y)
    rwa [neg_mul_neg, h0, h0, neg_mul_neg, ← neg_add, ← neg_add, sub_neg_eq_add,
      h1, add_right_inj, h0, neg_add_eq_sub, ← neg_sub, neg_eq_iff_add_eq_zero,
      ← two_mul, mul_eq_zero, or_iff_right hg0, sub_eq_zero, eq_comm] at h2
  ---- Now we show that `g` is multiplicative.
  replace h1 (x y) : g (x * y) = g x * g y := by
    specialize h1 x y; rwa [h0, h0, sub_self, add_zero, h, add_left_inj] at h1
  ---- Finally, join all the pieces together.
  exact ⟨RingHom.mk' ⟨⟨g, h⟩, h1⟩ h0, rfl⟩

end

end good'


/-- A function `g : ℝ → S` is good' with `g(-1) ≠ 1` if and only if
  `g` is a ring homomorphism. -/
theorem good'_Real_iff [Ring S] [IsDomain S] {g : ℝ → S} :
    (good' g ∧ g (-1) ≠ 1) ↔ ∃ φ : ℝ →+* S, g = φ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h, h0⟩; exact good'.Real_is_hom h h0
  · rintro ⟨φ, rfl⟩; refine ⟨RingHom_is_good' φ, λ hφ ↦ one_ne_zero' S ?_⟩
    replace hφ : φ 2 = 0 := calc
      _ = φ 1 + φ 1 := by rw [← φ.map_add, one_add_one_eq_two]
      _ = 1 - φ (-1) := by rw [φ.map_neg, sub_neg_eq_add, φ.map_one]
      _ = 0 := by rw [hφ, sub_self]
    replace hφ : φ 2 * φ 2⁻¹ = 0 := mul_eq_zero_of_left hφ _
    rwa [← φ.map_mul, mul_inv_cancel₀ two_ne_zero, φ.map_one] at hφ

/-- A function `f : ℝ → S` is good with `f(-1) ≠ 0` if and only if
  `f(x) = φ(x) - 1` for some ring homomorphism `φ : ℝ → S`. -/
theorem good_Real_iff [Ring S] [IsDomain S] {f : ℝ → S} :
    (good f ∧ f (-1) ≠ 0) ↔ ∃ φ : ℝ →+* S, f = (φ · - 1) :=
  calc good f ∧ f (-1) ≠ 0
  _ ↔ good' (f · + 1) ∧ f (-1) + 1 ≠ 1 := by rw [good_iff_good', add_ne_right]
  _ ↔ ∃ φ : ℝ →+* S, f + 1 = φ := good'_Real_iff
  _ ↔ ∃ φ : ℝ →+* S, f = φ - 1 := by simp only [eq_sub_iff_add_eq]

/-- Final solution -/
theorem final_solution {f : ℝ → ℝ} : (good f ∧ f (-1) ≠ 0) ↔ f = id - 1 :=
  good_Real_iff.trans Unique.exists_iff
