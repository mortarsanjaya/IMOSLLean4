/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

/-!
# IMO 2011 N5 (P5)

Let $f : ℤ → ℕ⁺$ be a function such that for any $x, y ∈ ℤ$,
$$ f(x - y) ∣ f(x) - f(y). $$
Prove that $f(x) ≤ f(y)$ implies $f(x) ∣ f(y)$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2011SL.pdf).

### Implementation details

We implement $f$ as a function from $ℤ$ to $ℤ$ such that $f(x) > 0$ for all $x ∈ ℤ$.
-/

namespace IMOSL
namespace IMO2011N5

/-- If `0 ≤ a < c` and `0 ≤ b < c`, then `|a - b| < c`. -/
theorem natAbs_sub_lt_of_nonneg_of_lt {a b : Int}
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

/-- Final solution -/
theorem final_solution {f : Int → Int}
    (hf : ∀ x, 0 < f x) (hf0 : ∀ x y, f (x - y) ∣ f x - f y)
    {x y : Int} (h : f x ≤ f y) : f x ∣ f y := by
  ---- We're done if `f(x) = f(y)`, so assume that `f(x) < f(y)`.
  obtain h0 | h0 : f x = f y ∨ f x < f y := Int.le_iff_eq_or_lt.mp h
  · exact ⟨1, h0.symm.trans (f x).mul_one.symm⟩
  ---- First, show that `f(x - y) ∣ f(y) - f(x)`.
  replace h : f (x - y) ∣ f y - f x := calc
    f (x - y) ∣ -(f x - f y) := Int.dvd_neg.mpr (hf0 x y)
    _ = f y - f x := Int.neg_sub _ _
  ---- Next, show that `f(x - y) < f(y)`.
  replace h : f (x - y) < f y := calc
    _ ≤ f y - f x := Int.le_of_dvd (Int.sub_pos_of_lt h0) h
    _ < f y := Int.sub_lt_self (f y) (hf x)
  ---- Next, show that `f(x) = f(x - y)` via `f(y) ∣ f(x) - f(x - y)`.
  replace h0 : f x = f (x - y) :=
    Int.eq_of_sub_eq_zero <| Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
      (by simpa only [Int.sub_sub_self] using hf0 x (x - y))
      (natAbs_sub_lt_of_nonneg_of_lt (Int.le_of_lt (hf x)) h0 (Int.le_of_lt (hf _)) h)
  ---- Finally, since `f(x) = f(x - y) ∣ f(x) - f(y)`, we get `f(x) ∣ f(y)`.
  replace hf0 : f (x - y) ∣ f x - f y := hf0 x y
  rwa [← h0, Int.sub_eq_add_neg, Int.dvd_add_right (Int.dvd_refl _), Int.dvd_neg] at hf0
