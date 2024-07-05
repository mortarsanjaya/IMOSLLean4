/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# IMO 2011 N5 (P5)

Let $G$ be an additive group.
Find all functions $f : G → ℕ^+$ such that for any $x, y ∈ G$,
$$ f(x - y) ∣ f(x) - f(y). $$

### Further directions

Generally, all functions satisfying the given condition can be determined.
The .tex file corresponding to this problem contains the solution to that.
I'm still interested in implementing this solution.
-/

namespace IMOSL
namespace IMO2011N5

variable [AddGroup G]

structure good (f : G → ℤ) : Prop where
  pos : ∀ x : G, 0 < f x
  dvd : ∀ x y : G, f (x - y) ∣ f x - f y





/-! ### Properties of good maps -/

namespace good

variable {f : G → ℤ} (hf : good f)

theorem nonneg (x) : 0 ≤ f x := (hf.pos x).le

theorem dvd_map_zero (x) : f x ∣ f 0 := by
  have h := hf.dvd x 0; rwa [sub_zero, dvd_sub_right (f x).dvd_refl] at h

theorem map_neg_eq : ∀ x, f (-x) = f x :=
  have h (x) : f (-x) ∣ f x := by
    have h := hf.dvd 0 x; rwa [zero_sub, dvd_sub_right (hf.dvd_map_zero (-x))] at h
  λ x ↦ Int.dvd_antisymm (hf.nonneg _) (hf.nonneg x) (h x)
    (by have h0 := h (-x); rwa [neg_neg] at h0)

theorem dvd_map_add_of_dvd_map (hx : n ∣ f x) (hy : n ∣ f y) : n ∣ f (x + y) := by
  have h := hf.dvd (x + y) y
  rw [add_sub_cancel_right] at h
  exact (Int.dvd_iff_dvd_of_dvd_sub (Int.dvd_trans hx h)).mpr hy

def DvdSubgroup (n : ℤ) (h : n ∣ f 0) : AddSubgroup G :=
  { carrier := {x | n ∣ f x}
    add_mem' := hf.dvd_map_add_of_dvd_map
    zero_mem' := h
    neg_mem' := λ h0 ↦ Int.dvd_trans h0 (hf.map_neg_eq _ ▸ Int.dvd_refl _) }

theorem map_dvd_of_lt (h : f x < f y) : f x ∣ f y := by
  have h0 := hf.dvd y x
  suffices f (y - x) = f x by rwa [this, dvd_sub_left (f x).dvd_refl] at h0
  rw [← sub_eq_zero, ← abs_eq_zero]
  refine Int.eq_zero_of_dvd_of_nonneg_of_lt (n := f y) (abs_nonneg _) ?_ ?_
  · have h1 (m n : ℤ) (h1 : 0 < m) (h2 : 0 < n) : |m - n| < m + n :=
      abs_sub_lt_of_nonneg_of_lt h1.le (m.lt_add_of_pos_right h2)
        h2.le (n.lt_add_of_pos_left h1)
    exact (h1 _ _ (hf.pos _) (hf.pos _)).trans_le
      (add_le_of_le_sub_right (Int.le_of_dvd (sub_pos_of_lt h) h0))
  · have h1 := hf.dvd (y - x) (-x)
    rwa [sub_neg_eq_add, sub_add_cancel, hf.map_neg_eq, ← dvd_abs] at h1

theorem map_dvd_of_le (h : f x ≤ f y) : f x ∣ f y :=
  h.lt_or_eq.elim hf.map_dvd_of_lt λ h ↦ h ▸ Int.dvd_refl _

end good





/-! ### Final solution (original version) -/

alias final_solution := good.map_dvd_of_le
