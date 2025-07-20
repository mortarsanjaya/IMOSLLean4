/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2017.A6.A6Basic
import IMOSLLean4.Extra.CharTwo.Ring
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# IMO 2017 A6 (P2, Value of non-periodic good functions on units)

Suppose that $R$ be an integral domain of characteristic $2$.
Then we show that $ι(f(x)) = 1 - x$ for any $x ∈ Rˣ$.
-/

namespace IMOSL
namespace IMO2017A6

open Extra

section

variable [Ring R] [AddCancelMonoid G]

/-- Good functions on division rings: a formula -/
theorem units_inv_formula'
    (ι : G → R) [FunLike F R G] [GoodFunClass F ι] (f : F) (c : Rˣ) :
    f (ι (f (c + 1)) * ι (f (c⁻¹ + 1))) = 0 := by
  rw [← add_right_cancel_iff, good_def, zero_add]
  apply congrArg f
  rw [mul_add_one, add_one_mul, Units.mul_inv, add_left_comm, add_assoc, ← add_assoc]

/-- Non-periodic good functions on division rings: a formula -/
theorem units_inv_formula
    (ι : G →+ R) [FunLike F R G] [NonperiodicGoodFunClass F ι] (f : F) (c : Rˣ) :
    ι (f (c + 1)) * ι (f (c⁻¹ + 1)) = 1 :=
  (map_eq_zero_iff_eq_one ι).mp (units_inv_formula' ι f c)

end


section

variable [Ring R] [IsDomain R] [CharTwo R] [AddCancelMonoid G] (ι : G →+ R)
  [FunLike F R G] [NonperiodicGoodFunClass F ι] (f : F)
include ι

theorem CharTwoDomain_incl_map_zero_eq_one : ι (f 0) = 1 :=
  CharTwo.mul_self_eq_one_iff.mp (incl_map_zero_mul_self ι f)

omit [IsDomain R] in
theorem CharTwoDomain_map_add_one (x) : f (x + 1) = f 0 + f x := by
  rw [← CharTwo.sub_eq_add, map_sub_one ι]

omit [IsDomain R] in
theorem CharTwoDomain_map_eq_step (a : R) (b : Rˣ) (h : f a = f b) :
    f (a * b⁻¹ + (a + b⁻¹)) = f (1 + (a + b⁻¹)) := by
  have X : ∀ x, f (x + 1) = f 0 + f x := CharTwoDomain_map_add_one ι f
  replace h : f (a + 1) = f (b + 1) := map_add_one_eq_of_map_eq ι h
  have h0 := good_def ι f (a + 1) (b⁻¹ + 1)
  rwa [h, units_inv_formula' ι f, zero_add, add_one_mul a, mul_add_one a, add_right_comm,
    X, ← add_assoc (_ + _), X, add_right_inj, eq_comm, ← add_rotate', add_assoc] at h0

end


section

variable [CommRing R] [IsDomain R] [CharTwo R] [AddCancelMonoid G] (ι : G →+ R)
  [FunLike F R G] [NonperiodicGoodFunClass F ι] (f : F)
include ι

theorem CharTwoDomain_units_injective {a b : Rˣ} (h : f a = f b) : a = b := by
  have X : ∀ x, f (x + 1) = f 0 + f x := CharTwoDomain_map_add_one ι f
  have X0 {c} : f c = 0 ↔ c = 1 := map_eq_zero_iff_eq_one ι
  have X1 {c} : f c = f 0 ↔ c = 0 := by
    rw [← map_zero_add_map_add_one ι, add_eq_left, X0, add_eq_right]
  have h0 : (a.1 * b⁻¹ + (a + b⁻¹)) * (b * a⁻¹ + (b + a⁻¹))
      = (1 + (a + b⁻¹)) * (1 + (b + a⁻¹)) := calc
    _ = (a.1 * b⁻¹) * (b * a⁻¹) + (a * b⁻¹) * (b + a⁻¹)
        + ((a + b⁻¹) * (b * a⁻¹) + (a + b⁻¹) * (b + a⁻¹)) := by
      rw [add_mul, mul_add, mul_add (a.1 + b⁻¹)]
    _ = 1 + (a + b⁻¹) + ((b + a⁻¹) + (a + b⁻¹) * (b + a⁻¹)) := by
      have h0 (c d : Rˣ) : (c.1 * d⁻¹) * (d + c⁻¹) = c + d⁻¹ := by
        rw [mul_add, d.inv_mul_cancel_right, mul_rotate, c.inv_mul_cancel_right]
      refine congrArg₂ _ (congrArg₂ _ ?_ (h0 a b)) (congrArg₂ _ ?_ rfl)
      · rw [mul_assoc, b.inv_mul_cancel_left, a.mul_inv]
      · rw [mul_comm, h0 b a]
    _ = _ := by rw [mul_one_add, one_add_mul]
  replace h0 : f (a * b⁻¹ + (a + b⁻¹) + (b * a⁻¹ + (b + a⁻¹)))
      = f (1 + (a + b⁻¹) + (1 + (b + a⁻¹))) := by
    have h1 := CharTwoDomain_map_eq_step ι f b a h.symm
    have h2 := CharTwoDomain_map_eq_step ι f a b h
    exact (map_add_eq_iff_map_mul_eq ι h2 h1).mpr (congrArg f h0)
  replace h : (a.1 + b + 1) * (b⁻¹ + a⁻¹ + 1) + 1
      = a * b⁻¹ + (a + b⁻¹) + (b * a⁻¹ + (b + a⁻¹)) := calc
    _ = (a.1 + b) * (b⁻¹ + a⁻¹) + ((a + b) + (b⁻¹ + a⁻¹)) := by
      rw [add_one_mul (a.1 + b), mul_add_one (a.1 + b), add_assoc, add_assoc,
        CharTwo.add_add_cancel_right, ← add_assoc (a.1 + b), ← add_assoc]
    _ = (a * b⁻¹ + b * a⁻¹) + ((a + b⁻¹) + (b + a⁻¹)) := by
      refine congrArg₂ _ ?_ (add_add_add_comm _ _ _ _)
      rw [add_mul, mul_add, mul_add, a.mul_inv, b.mul_inv,
        ← add_assoc, CharTwo.add_add_cancel_right]
    _ = _ := by rw [add_add_add_comm]
  rw [← h, X, add_add_add_comm, add_add_add_comm a.1, add_add_add_comm,
    add_comm 1, add_comm 1, ← good_def ι, ← add_assoc, add_eq_right,
    ← X, X0, add_eq_right, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · replace h0 : f _ = 0 := map_eq_zero_of_incl_map_eq_zero ι h0
    rwa [X0, add_eq_right, CharTwo.add_eq_zero_iff_eq, Units.val_inj] at h0
  · replace h0 : f _ = 0 := map_eq_zero_of_incl_map_eq_zero ι h0
    rwa [X0, add_eq_right, CharTwo.add_eq_zero_iff_eq,
      Units.val_inj, inv_inj, eq_comm] at h0

theorem CharTwoDomain_units_incl_map_eq (x : Rˣ) : ι (f x) = 1 - x := by
  let c : Rˣ := ⟨ι (f (x + 1)), _, units_inv_formula ι f x,
    by simpa only [inv_inv] using units_inv_formula ι f x⁻¹⟩
  have X : ι (f 0) = 1 := CharTwoDomain_incl_map_zero_eq_one ι f
  suffices c = x by
    rw [CharTwo.sub_eq_add, ← map_zero_add_map_add_one ι, ι.map_add, X, add_right_inj]
    exact congrArg Units.val this
  have h : ι (f c + f (x + 1)) = ι (f 0) := by simpa only [X, one_mul]
    using (congrArg ι (map_incl_map_zero_mul_incl_map_add_map ι f (x + 1)))
  rw [ι.map_add, ← CharTwo.sub_eq_add, sub_eq_iff_eq_add,
    ← ι.map_add, map_zero_add_map_add_one ι] at h
  exact CharTwoDomain_units_injective ι f (map_eq_of_incl_map_eq ι h)

end
