/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Basic

/-!
# IMO 2011 N5 (P5)

Let $G$ be an (not necessarily abelian) additive group.
Let $f : G → ℕ⁺$ be a function such that for any $x, y ∈ G$,
$$ f(x - y) ∣ f(x) - f(y). $$
Prove that $f(x) ≤ f(y)$ implies $f(x) ∣ f(y)$.

### Solution

We adapt Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2011SL.pdf),
  but we need to make sure that our solution works without assuming that $G$ is abelian.
This will be a bit confusing; readers may assume that $G$ is abelian.

First, plugging $y = 0$ yields $f(x) ∣ f(0)$ for all $x ∈ G$.
Plugging $x = 0$ then yields $f(-y) ∣ f(y)$ for all $y ∈ G$.
Then $f(-y) ∣ f(y)$ and $f(y) ∣ f(-y)$ yields $f(-y) = f(y)$ for all $y ∈ G$.

Now we go back to the goal.
Since $f(y - x) ∣ f(y) - f(x)$, it suffices to show that $f(y - x) = f(x)$.
We may assume that $f(x) < f(y)$, as the case $f(x) = f(y)$ is obvious.
Then $0 < f(y - x) ≤ f(y) - f(x) < f(y)$.
But the given property of $f$ also yields $f(y) ∣ f(y - x) - f(-x) = f(y - x) - f(x)$.
Since $0 < f(x), f(y - x) < f(y)$, this forces $f(x) = f(y - x)$, as desired.

### Implementation details

We implement $f$ as a function from $G$ to $ℤ$ such that $f(x) > 0$ for all $x ∈ G$.
-/

namespace IMOSL
namespace IMO2011N5

/-- If `0 ≤ a < c` and `0 ≤ b < c`, then `|a - b| < c`. -/
theorem natAbs_sub_lt_of_nonneg_of_lt {a b : ℤ}
    (ha0 : 0 ≤ a) (hac : a < c) (hb0 : 0 ≤ b) (hbc : b < c) :
    (a - b).natAbs < c.natAbs := by
  ---- Divide into two cases: `a ≤ b` and `b ≤ a`.
  obtain h | h : a ≤ b ∨ b ≤ a := Int.le_total a b
  ---- If `a ≤ b`, then `|a - b| = b - a ≤ b < c`.
  · calc (a - b).natAbs
      _ = (b - a).natAbs := by rw [← Int.natAbs_neg, Int.neg_sub]
      _ < c.natAbs := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.sub_nonneg_of_le h)
        (Int.lt_of_le_of_lt (Int.sub_le_self b ha0) hbc)
  ---- If `b ≤ a`, then `|a - b| = a - b ≤ a < c`.
  · exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.sub_nonneg_of_le h)
      (Int.lt_of_le_of_lt (Int.sub_le_self a hb0) hac)


/-- A function `f : G → ℤ` is good if `f` only takes positive values and
  `f(x - y) ∣ f(x) - f(y)` for all `x, y ∈ G`. -/
structure good [Sub G] (f : G → ℤ) where
  pos x : 0 < f x
  spec x y : f (x - y) ∣ f x - f y


namespace good

variable [AddGroup G] {f : G → ℤ} (hf : good f)
include hf

/-- For any `x ∈ G`, we have `0 ≤ f(x)`. -/
theorem nonneg (x) : 0 ≤ f x :=
  Int.le_of_lt (hf.pos x)

/-- For any `x ∈ G`, we have `f(x) ∣ f(0)`. -/
theorem map_dvd_map_zero (x) : f x ∣ f 0 := by
  have h : f (x - 0) ∣ f x - f 0 := hf.spec x 0
  rwa [sub_zero, Int.sub_eq_add_neg, Int.dvd_add_right (Int.dvd_refl _), Int.dvd_neg] at h

/-- For any `x ∈ G`, we have `f(-x) = f(x)`. -/
theorem map_neg : ∀ x : G, f (-x) = f x := by
  ---- Reduce to `f(x) ∣ f(-x)` for any `x ∈ G`.
  suffices ∀ x, f (-x) ∣ f x
    from λ x ↦ Int.dvd_antisymm (hf.nonneg (-x)) (hf.nonneg x)
      (this x) (by simpa only [neg_neg] using this (-x))
  ---- Now `f(x) ∣ f(-x)` follows by substituting `y = 0` since `f(-x) ∣ f(0)`.
  intro x
  have h : (f (0 - x) : ℤ) ∣ f 0 - f x := hf.spec 0 x
  rwa [zero_sub, ← Int.dvd_neg, Int.neg_sub,
    ← Int.dvd_add_left (hf.map_dvd_map_zero _), Int.sub_add_cancel] at h

/-- For any `x, y ∈ G`, if `f(x) < f(y)`, then `f(x) ∣ f(y)`. -/
theorem map_dvd_of_map_lt (h : f x < f y) : f x ∣ f y := by
  ---- First notice that `f(y - x) ∣ f(y) - f(x)`.
  have h0 : f (y - x) ∣ f y - f x := hf.spec y x
  ---- It now suffices to show that `f(y - x) = f(x)`.
  suffices f (y - x) = f x by
    rw [← this, Int.dvd_iff_dvd_of_dvd_sub h0, this]
    exact Int.dvd_refl (f x)
  ---- From `f(y - x) ∣ f(y) - f(x)`, we have `f(y - x) < f(y)`.
  replace h0 : f (y - x) < f y :=
    calc f (y - x)
    _ ≤ f y - f x := Int.le_of_dvd (Int.sub_pos_of_lt h) h0
    _ < f y := Int.sub_lt_self _ (hf.pos x)
  ---- On the other hand, we also have `f(y) ∣ f(y - x) - f(x)` since `f(x) = f(-x)`.
  have h1 : f y ∣ f (y - x) - f x :=
    calc f y
    _ = f (y - x - (-x)) := by rw [sub_neg_eq_add, sub_add_cancel]
    _ ∣ f (y - x) - f (-x) := hf.spec _ _
    _ = f (y - x) - f x := by rw [hf.map_neg]
  ---- Since `|f(y - x) - f(x)| < f(y)`, this forces `f(y - x) = f(x)`, as desired.
  exact Int.eq_of_sub_eq_zero <| Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h1
    (natAbs_sub_lt_of_nonneg_of_lt (hf.nonneg _) h0 (hf.nonneg _) h)

/-- For any `x, y ∈ G` such that `f(x) ≤ f(y)`, we have `f(x) ∣ f(y)`. -/
theorem map_dvd_of_map_le (h : f x ≤ f y) : f x ∣ f y :=
  (Int.le_iff_eq_or_lt.mp h).elim (λ h ↦ h ▸ Int.dvd_refl _) hf.map_dvd_of_map_lt

end good


/-- Final solution -/
alias final_solution := good.map_dvd_of_map_le
