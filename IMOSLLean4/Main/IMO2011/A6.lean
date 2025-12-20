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

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2011SL.pdf),
  but we will make shortcuts and modify some parts of the proof.
Therefore, we will have to describe our version of the solution here.

As in the official solution, we get $x f(x) ≤ 0$ for all $x ∈ R$.
Now plugging $y = 0$ to the initial inequality gives $f(x) ≤ f(f(x))$.
If $f(x) > 0$, then $f(f(x)) ≥ f(x) > 0$ yields $0 < f(x) f(f(x)) ≤ 0$; contradiction.
Thus, we must have $f(x) ≤ 0$ for all $x ∈ R$.
In particular, combining with $x f(x) ≤ 0$ yields $f(x) = 0$ whenever $x < 0$.

Finally, pick any $y < 0$, say $y = -1$.
Then $0 = f(y) ≤ f(f(y)) = f(0) ≤ 0$, so $f(0) = 0$.
-/

namespace IMOSL
namespace IMO2011A6

/-- A function `f : R → R` is good if `f(x + y) ≤ y f(x) + f(f(x))` for any `x, y ∈ R`. -/
def good [Ring R] [Preorder R] (f : R → R) :=
  ∀ x y : R, f (x + y) ≤ y * f x + f (f x)


namespace good

/-- For any `x, t ∈ R`, we have `f(t) ≤ (t - x) f(x) + f(f(x))`. -/
theorem alt [Ring R] [Preorder R] {f : R → R} (hf : good f) (x t : R) :
    f t ≤ (t - x) * f x + f (f x) := calc
  _ = f (x + (t - x)) := congrArg f (add_sub_cancel x t).symm
  _ ≤ _ := hf x (t - x)

/-- For any `x, t ∈ R`, we have `f(t) - f(f(x)) ≤ (t - x) f(x)`. -/
theorem alt' [Ring R] [LinearOrder R] [IsOrderedAddMonoid R]
    {f : R → R} (hf : good f) (x t : R) :
    f t - f (f x) ≤ (t - x) * f x := calc
  _ ≤ ((t - x) * f x + f (f x)) - f (f x) := sub_le_sub_right (hf.alt x t) _
  _ = _ := add_sub_cancel_right _ _

/-- For any `a ∈ R`, we have `a f(a) ≤ 0`. -/
theorem self_mul_map_nonpos [CommRing R] [LinearOrder R] [IsOrderedAddMonoid R]
    {f : R → R} (hf : good f) (a : R) : a * f a ≤ 0 := by
  let b : R := 2 * f a
  apply neg_nonneg.mp
  /- Use `good.alt` to show `(f(a) - b) f(b) + (f(b) - a) f(a) ≥ 0`,
    and show that the right hand side rearranges to `-a f(a)`. -/
  calc
  0 = f (f a) - f (f b) + (f (f b) - f (f a)) := by rw [sub_add_sub_cancel, sub_self]
  _ ≤ (f a - b) * f b + (f b - a) * f a := add_le_add (hf.alt' _ _) (hf.alt' _ _)
  _ = (f a - (f a + f a)) * f b + (f b - a) * f a := by rw [← two_mul]
  _ = -(f a * f b) + (f b - a) * f a := by rw [sub_add_cancel_right, neg_mul]
  _ = -(a * f a) := by rw [mul_comm, sub_mul, sub_eq_add_neg, neg_add_cancel_left]

/-- For any `x ∈ R`, we have `f(f(x)) ≥ f(x)`. -/
theorem map_le_map_map [Ring R] [Preorder R] {f : R → R} (hf : good f) (x : R) :
    f x ≤ f (f x) := calc
  _ = f (x + 0) := congrArg f (add_zero x).symm
  _ ≤ 0 * f x + f (f x) := hf x 0
  _ = f (f x) := by rw [zero_mul, zero_add]


variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {f : R → R} (hf : good f)
include hf

/-- For any `x ∈ R`, we have `f(x) ≤ 0`. -/
theorem map_nonpos (x : R) : f x ≤ 0 := by
  ---- Suppose that `f(x) > 0`.
  refine le_of_not_gt λ h ↦ ?_
  ---- Then `f(f(x)) ≥ f(x) > 0` yields `f(x) f(f(x)) > 0`.
  have h0 : 0 < f x * f (f x) := mul_pos h (h.trans_le (hf.map_le_map_map x))
  ---- But we had `a f(a) ≤ 0` for all `a`, so `f(x) f(f(x)) ≤ 0`; contradiction.
  exact h0.not_ge (hf.self_mul_map_nonpos (f x))

/-- For any `x ∈ R` with `x < 0`, we have `f(x) = 0`. -/
theorem map_eq_zero_of_neg {x : R} (hx : x < 0) : f x = 0 :=
  ---- This holds since `x f(x) ≤ 0` implies `f(x) ≥ 0` for `x < 0`.
  (hf.map_nonpos x).antisymm (nonneg_of_mul_nonpos_right (hf.self_mul_map_nonpos x) hx)

/-- We have `f(0) = 0`. -/
theorem map_zero : f 0 = 0 := by
  ---- It suffices to show `f(0) ≥ 0`.
  apply (hf.map_nonpos 0).antisymm
  ---- Pick any `y < 0`.
  obtain ⟨y, hy⟩ : ∃ y : R, y < 0 := ⟨-1, neg_one_lt_zero⟩
  ---- Then `f(y) = 0`, so `f(y) ≤ f(f(y))` yields `f(0) ≥ 0`.
  simpa only [hf.map_eq_zero_of_neg hy] using hf.map_le_map_map y

/-- For any `x ∈ R` with `x ≤ 0`, we have `f(x) = 0`. -/
theorem map_eq_zero_of_nonpos {x : R} (hx : x ≤ 0) : f x = 0 :=
  hx.lt_or_eq.elim hf.map_eq_zero_of_neg (λ hx ↦ hx ▸ hf.map_zero)

end good


/-- Final solution -/
alias final_solution := good.map_eq_zero_of_nonpos
