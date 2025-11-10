/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Nat.Cast.Commute

/-!
# IMO 2009 A5

Let $R$ be a totally ordered ring.
Prove that there does not exist a function $f : R → R$ such that for all $x, y ∈ R$,
$$ f(x - f(y)) ≤ y f(x) + x. $$

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
Over the more general setting, some bounds need to be weakened.
Namely, instead of proving that $f(x) ≤ 0$ for all $x ∈ R$, we settle with
  $f(x)$ being small in the sense that $yf(x) ≤ 1$ for all $y ∈ R$ with $y ≥ 0$.
(Actually, we only need $3f(x) ≤ 1$.)
We also do not prove $f(x) ≤ x$ for all $x ∈ R$.
Note that this solution works even if $R$ is not commutative.

As in the official solution, we get $-f(0) - 1 ≤ f(y) ≤ y + f(0)$ for all $y ∈ R$.
Now we show that $yf(x) ≤ 1$ for all $x, y ∈ R$ with $y ≥ 0$.
If $f(x) ≤ 0$, then we are done, so now suppose that $f(x) > 0$.
Take a very large $C$ such that $x + C > f(0)$ and $C ≥ y$.
Then we have $-C f(x) + x ≥ f(x - f(-C))$.
Since $x - f(-C) ≥ x + C - f(0) > 0$, we get
$$ -C f(x) + x > -f(0) - 1 \implies x + f(0) + 1 ≥ Cf(x) ≥ yf(x). $$
Note that this inequality holds for any $y ∈ R$.
In particular, $x + f(0) + 1 ≥ f(x) > 0$.
Replacing $y$ with $(x + f(0) + 1)y$ gives us $yf(x) ≤ 1$ for all $y$, as desired.

Now fix some $y > 0$, and set $x = f(y) - 1$.
Then we have
$$ f(-1) ≤ yf(f(y) - 1) + f(y) - 1 ≤ y(f(y) - 1 + f(0)) + f(y) - 1. $$
Now multiply both sides by $3$.
Since $y > 0$, we get
$$ 3f(-1) ≤ y(3f(y) - 3 + 3f(0)) + 3f(y) - 3 ≤ y(1 - 3 + 1) + 1 - 3 = -y - 2. $$
That is, we have $y ≤ -3f(-1) - 2$.
Taking any $y > \max\\{0, -3f(-1) - 2\\}$ then yields a contradiction.
-/

namespace IMOSL
namespace IMO2009A5

/-- Final solution -/
theorem final_solution [Ring R] [LinearOrder R] [IsStrictOrderedRing R] (f : R → R) :
    ¬∀ x y, f (x - f y) ≤ y * f x + x := by
  intro hf

  ---- First show that `f(y) ≤ y + f(0)` for all `y ∈ R`.
  have hf1 (y) : f y ≤ y + f 0 := by
    specialize hf (y + f 0) 0
    rwa [zero_mul, zero_add, add_sub_cancel_right] at hf

  ---- Next show that `f(y) ≥ -f(0) - 1` whenever `y > 0`.
  have hf2 (y) (hy : 0 < y) : -(f 0 + 1) ≤ f y := by
    replace hf : f (f y - f y) ≤ y * f (f y) + (y + f 0) :=
      (hf (f y) y).trans (add_le_add_left (hf1 y) _)
    rw [sub_self, ← add_assoc, le_add_iff_nonneg_left, ← mul_add_one y,
      mul_nonneg_iff_of_pos_left hy, ← neg_le_iff_add_nonneg] at hf
    rw [neg_add, neg_add_le_iff_le_add, add_comm]
    exact hf.trans (hf1 _)

  ---- Prove that `yf(x) ≤ 1` for any `x, y ∈ R` with `y ≥ 0`.
  replace hf2 (y) (hy : 0 ≤ y) (x) : y * f x ≤ 1 := by
    -- If `f(x) ≤ 0`, we are done, so now assume that `f(x) > 0`.
    refine (lt_or_ge 0 (f x)).elim (λ h ↦ ?_)
      (λ h ↦ (mul_nonpos_of_nonneg_of_nonpos hy h).trans zero_le_one)
    -- Next show that `A = x + f(0) + 1 ≥ yf(x)` for all `y ∈ R`.
    let A : R := x + (f 0 + 1)
    replace hf (y) : y * f x ≤ A := by
      -- First pick some `C ≥ y` with `x + C > f(0)`.
      obtain ⟨C, h0, h1⟩ : ∃ C ≥ y, f 0 < x + C := by
        refine ⟨max y (f 0 + 1 - x), le_max_left _ _, ?_⟩
        rw [← max_add_add_left, add_sub_cancel, lt_max_iff, lt_add_iff_pos_right]
        right; exact zero_lt_one
      -- Note that `x - f(-C) > 0`.
      replace h1 : 0 < x - f (-C) :=
        sub_pos_of_lt ((hf1 _).trans_lt (neg_add_lt_iff_lt_add'.mpr h1))
      -- Then `-C f(x) + x ≥ f(x - f(-C)) ≥ -f(0) - 1`.
      replace h1 : -(f 0 + 1) ≤ -C * f x + x := calc
        _ ≤ f (x - f (-C)) := hf2 _ h1
        _ ≤ -C * f x + x := hf _ _
      -- Thus `yf(x) ≤ Cf(x) ≤ x + f(0) + 1 = A`.
      rw [neg_le_iff_add_nonneg, add_assoc, neg_mul, le_neg_add_iff_add_le, add_zero] at h1
      exact (mul_le_mul_of_nonneg_right h0 h.le).trans h1
    -- Finally, note that `A > 0`, and replace `y → Ay`.
    replace hf1 : A > 0 := h.trans_le ((one_mul (f x)).symm.trans_le (hf 1))
    specialize hf (A * y)
    rwa [mul_assoc, mul_le_iff_le_one_right hf1] at hf
  ---- Specialize to the case `y = 3`; we have `3f(x) ≤ 1` for any `x ∈ R`.
  replace hf2 (x) : 3 * f x ≤ 1 := hf2 3 zero_le_three x

  ---- Next, get `y ≤ B` whenever `y ≥ 0`, where `B = -3f(-1) - 2`.
  let B := -(3 * f (-1) + 2)
  replace hf (y : R) (hy : y ≥ 0) : y ≤ B := by
    -- First get `f(-1) ≤ y(f(y) - 1 + f(0)) + f(y) - 1`.
    have h : f (-1) ≤ y * (f y - 1 + f 0) + (f y - 1) := calc
      f (-1) = f (f y - 1 - f y) := by rw [sub_sub_cancel_left]
      _ ≤ y * f (f y - 1) + (f y - 1) := hf (f y - 1) y
      _ ≤ y * (f y - 1 + f 0) + (f y - 1) :=
        add_le_add_right (mul_le_mul_of_nonneg_left (hf1 (f y - 1)) hy) _
    -- Next, multiply both sides by `3` and use the inequality `3f(x) ≤ 1` for all `x`.
    replace h : 3 * f (-1) ≤ -y - 2 := by
      calc 3 * f (-1)
        _ ≤ 3 * (y * (f y - 1 + f 0) + (f y - 1)) :=
          mul_le_mul_of_nonneg_left h zero_le_three
        _ = y * (3 * f y - 3 + 3 * f 0) + (3 * f y - 3) := by
          rw [mul_add, ← mul_assoc, Commute.ofNat_left 3, mul_assoc, mul_add, mul_sub_one]
        _ ≤ y * (-2 + 1) + (-2) := ?_
        _ = -y - 2 := by rw [sub_eq_add_neg, add_left_inj, ← one_add_one_eq_two,
          neg_add_rev, neg_add_cancel_right, mul_neg, mul_one]
      -- We left out `y(3 f(y) - 3 + 3 f(0)) + (3 f(y) - 3) ≤ -y - 2`.
      replace h : 3 * f y - 3 ≤ -2 := calc
        _ ≤ 1 - 3 := sub_le_sub_right (hf2 y) 3
        _ = -2 := by rw [← two_add_one_eq_three, sub_add_cancel_right]
      exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add h (hf2 0)) hy) h
    -- We are done by a bit of rearranging.
    rwa [le_sub_iff_add_le, ← neg_le_neg_iff, neg_neg] at h

  ---- Take `y` large enough; contradiction.
  specialize hf (max 0 (B + 1)) (le_max_left 0 (B + 1))
  exact hf.not_gt (lt_max_of_lt_right (lt_add_one B))
