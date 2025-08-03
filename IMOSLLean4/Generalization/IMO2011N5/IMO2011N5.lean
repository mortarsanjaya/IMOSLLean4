/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Int

/-!
# IMO 2011 N5 (P5, Generalization)

Let $G$ be an additive group.
Find all functions $f : G → ℕ⁺$ such that for any $x, y ∈ G$,
$$ f(x - y) ∣ f(x) - f(y). $$

### Answer

Consider a strict chain $G = G_0 > G_1 > G_2 > … > G_k$ of subgroups of $G$.
Let $n_0, n_1, n_2, …, n_k$ be positive integers with $n_1, n_2, …, n_k > 1$.
Set $f(x) = n_0 n_1 … n_j$, where $j$ is the largest index such that $x ∈ G_j$.
Then $f$ is a good function, and all good functions arise uniquely via this construction.

### Implementation

We implement the original condition as `good`.
The strict chain is implemented as a separate inductive structure `GoodFunData`.
To construct the inductive structure from am explicit good function, instead of
  constructing the set of elements divisible by a fixed positive integer as a subgroup,
  we only construct the subgroup of elements whose value is not a minimal value.
-/

namespace IMOSL
namespace Generalization
namespace IMO2011N5

/-! ### Extra lemmas -/

/-- A small lemma that interchanges divisibility over `ℕ+` and `ℤ`. -/
theorem PNat_IntCast_dvd_iff {m n : ℕ+} : (m : ℤ) ∣ n ↔ m ∣ n := by
  rw [Int.natCast_dvd_natCast, ← PNat.dvd_iff]



/-! ### Good functions and their properties -/

/-- A function `f : G → ℕ+` is `good` if `f(x - y) ∣ f(x) - f(y)` for any `x, y ∈ G`. -/
def good [Sub G] (f : G → ℕ+) := ∀ x y, (f (x - y) : ℤ) ∣ f x - f y



namespace good

variable [AddGroup G] {f : G → ℕ+} (hf : good f)
include hf

/-- For any `x ∈ G`, we have `f(x) ∣ f(0)`. -/
theorem map_dvd_map_zero (x : G) : f x ∣ f 0 := by
  have h : (f x : ℤ) ∣ f x - f 0 := by simpa only [sub_zero] using hf x 0
  rw [← PNat_IntCast_dvd_iff, ← Int.dvd_iff_dvd_of_dvd_sub h]

/-- For any `x ∈ G`, we have `f(-x) = f(x)`. -/
theorem map_neg : ∀ x : G, f (-x) = f x := by
  ---- Reduce to `f(x) ∣ f(-x)` for any `x ∈ G`.
  suffices ∀ x, f (-x) ∣ f x
    from λ x ↦ PNat.dvd_antisymm (this x) (by simpa only [neg_neg] using this (-x))
  ---- Now `f(x) ∣ f(-x)` follows by substituting `y = 0` since `f(-x) ∣ f(0)`.
  intro x
  have h : (f (-x) : ℤ) ∣ f 0 - f x := by simpa only [zero_sub] using hf 0 x
  rw [← PNat_IntCast_dvd_iff, ← Int.dvd_iff_dvd_of_dvd_sub h, PNat_IntCast_dvd_iff]
  exact hf.map_dvd_map_zero (-x)

/-- For any `x, y ∈ G` and `n ∈ ℕ+` such that `n ∣ f(x)` and `n ∣ f(y)`,
  we have `n ∣ f(x + y)`. -/
theorem dvd_map_add {x y : G} (hx : n ∣ f x) (hy : n ∣ f y) : n ∣ f (x + y) := by
  -- This follows from `n ∣ f(x) ∣ f(x + y) - f(y)` and `n ∣ f(y)`.
  have h : (n : ℤ) ∣ f (x + y) - f y :=
    calc (n : ℤ)
    _ ∣ f x := PNat_IntCast_dvd_iff.mpr hx
    _ = f (x + y - y) := by rw [add_sub_cancel_right]
    _ ∣ f (x + y) - f y := hf (x + y) y
  rwa [← PNat_IntCast_dvd_iff, Int.dvd_iff_dvd_of_dvd_sub h, PNat_IntCast_dvd_iff]

/-- For any `x, y ∈ G` such that `f(x) < f(y)`, we have `f(x) ∣ f(y)`. -/
theorem map_dvd_of_map_lt {x y : G} (h : f x < f y) : f x ∣ f y := by
  ---- First show that `f(y - x) ∣ f(y) - f(x)`.
  have h0 : (f (y - x) : ℤ) ∣ f y - f x := hf y x
  ---- Now show that `f(y - x) = f(x)`.
  replace h : (f (y - x) : ℤ) = f x := by
    refine Int.eq_of_sub_eq_zero (Int.eq_zero_of_abs_lt_dvd (m := f y) ?_ ?_)
    -- First show that `f(y) ∣ f(y - x) - f(x)` via `f(y) ∣ f(y - x) - f(-x)`.
    · simpa only [sub_neg_eq_add, sub_add_cancel, hf.map_neg] using hf (y - x) (-x)
    -- Now show that `|f(y - x) - f(x)| < f(y)` via `f(x), f(y - x) < f(y)`.
    · refine Int.abs_sub_lt_of_lt_lt h (Int.ofNat_lt.mp ?_)
      calc (f (y - x) : ℤ)
        _ ≤ f y - f x := Int.le_of_dvd (Int.sub_pos_of_lt (Int.ofNat_lt.mpr h)) h0
        _ < f y := Int.sub_lt_self _ (Int.natCast_pos.mpr (f x).pos)
  ---- Then `f(x) = f(y - x) ∣ f(y) - f(x)`, so `f(x) ∣ f(y)`.
  rw [← PNat_IntCast_dvd_iff, ← h, Int.dvd_iff_dvd_of_dvd_sub h0, h]

/-- For any `x, y ∈ G` such that `f(x) ≤ f(y)`, we have `f(x) ∣ f(y)`. -/
theorem map_dvd_of_map_le {x y : G} (h : f x ≤ f y) : f x ∣ f y :=
  h.eq_or_lt.elim (λ h ↦ h ▸ dvd_refl _) hf.map_dvd_of_map_lt

end good
