/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2021.A8.A8Defs
import Mathlib.Tactic.Ring

/-!
# IMO 2021 A8 (Some good functions)

We show that if $R$ is commutative, then any homomorphism and their cubes are good functions.
-/

namespace IMOSL
namespace IMO2021A8

variable [CommRing R] [NonAssocRing S] (φ : R →+* S) (s : S)

theorem hom_is_good : good φ := λ a b c ↦ by
  simp only [← φ.map_sub, ← φ.map_mul]
  apply congrArg φ; ring

theorem hom_cube_is_good : good (λ x ↦ φ (x ^ 3)) := λ a b c ↦ by
  simp only [← φ.map_sub, ← φ.map_mul]
  apply congrArg φ; ring

theorem hom_add_const_is_good : good (λ x ↦ φ x + s) :=
  (hom_is_good φ).add_const s

theorem hom_cube_add_const_is_good : good (λ x ↦ φ (x ^ 3) + s) :=
  (hom_cube_is_good φ).add_const s

theorem neg_hom_is_good : good (λ x ↦ -φ x) :=
  (hom_is_good φ).neg

theorem neg_hom_cube_is_good : good (λ x ↦ -φ (x ^ 3)) :=
  (hom_cube_is_good φ).neg

theorem neg_hom_add_const_is_good : good (λ x ↦ -φ x + s) :=
  (neg_hom_is_good φ).add_const s

theorem neg_hom_cube_add_const_is_good : good (λ x ↦ -φ (x ^ 3) + s) :=
  (neg_hom_cube_is_good φ).add_const s


theorem hom_is_NormalizedGood : NormalizedGood φ where
  is_good := hom_is_good φ
  map_zero := φ.map_zero

theorem hom_cube_is_NormalizedGood : NormalizedGood (λ x ↦ φ (x ^ 3)) where
  is_good := hom_cube_is_good φ
  map_zero := by rw [zero_pow (Nat.succ_ne_zero 2), φ.map_zero]

theorem neg_hom_is_NormalizedGood : NormalizedGood (λ x ↦ -φ x) where
  is_good := neg_hom_is_good φ
  map_zero := by rw [φ.map_zero, neg_zero]

theorem neg_hom_cube_is_NormalizedGood : NormalizedGood (λ x ↦ -φ (x ^ 3)) where
  is_good := neg_hom_cube_is_good φ
  map_zero := by rw [zero_pow (Nat.succ_ne_zero 2), φ.map_zero, neg_zero]
