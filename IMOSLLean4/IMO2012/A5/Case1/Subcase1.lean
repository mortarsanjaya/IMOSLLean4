/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.Case1.Basic
import Mathlib.Tactic.Ring

/-!
# IMO 2012 A5, Subcase 1.1: `f(-1) = -2 ≠ 0`

This file solves Subcase 1.1.
-/

namespace IMOSL
namespace IMO2012A5

/-- Auxiliary lemma: `2 ≠ 0` -/
private theorem case1_1_S_two_ne_zero {S : Type _} [AddGroup S]
    {a b : S} (h : a ≠ 0) (h0 : a = -b) : (b : S) ≠ 0 :=
  neg_ne_zero.mp λ h1 ↦ h <| h0.trans h1

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) ≠ 0) (h1 : f (-1) = -2)

/-- (4.1) -/
theorem case1_1_lem1 (x : R) : f (-x) + f x = -2 :=
  (ne_or_eq (f (x + 1)) 0).elim
    (λ h2 ↦ h1 ▸ case1_map_add_one_ne_zero_imp h h0 h2)
    (λ h2 ↦ by have h3 := case1_map_add_one_eq_zero_imp h h0 h2
               rw [h3.1, h3.2, ← neg_add, one_add_one_eq_two])

/-- (4.2) -/
theorem case1_1_lem2 (x : R) : f (x + 1) = f x + 1 := by
  rw [← sub_eq_iff_eq_add]
  apply mul_right_cancel₀ h0
  rw [sub_one_mul, ← map_neg_sub_map2 h, h1, mul_neg, mul_two,
    ← case1_1_lem1 h h0 h1 x, ← sub_sub, sub_sub_cancel_left, neg_add']

/-- Solution for the current subcase (`x ↦ φ(x) - 1`) -/
theorem case1_1_IsAnswer : IsAnswer f :=
  IsAnswer_of_add_one_additive h λ x y ↦ by
    apply mul_right_cancel₀ (case1_1_S_two_ne_zero h0 h1)
    have h2 := λ t ↦ eq_sub_of_add_eq (case1_1_lem1 h h0 h1 t)
    have h3 := case1_map_add_main_eq2 h x y
    rw [h1, case1_1_lem2 h h0 h1, mul_neg, neg_neg, add_one_mul (α := S)] at h3
    rw [eq_sub_of_add_eq h3, h2, h2]
    ring
