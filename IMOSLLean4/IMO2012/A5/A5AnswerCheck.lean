/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5Defs
import Mathlib.Tactic.Ring

/-!
# IMO 2012 A5 (Answer Checking)

This file checks that the claimed answers satisfy functional equation.
-/

namespace IMOSL
namespace IMO2012A5

/-- The zero map is good. -/
theorem zero_is_good [Ring R] [Ring S] : good (0 : R → S) :=
  λ _ _ ↦ (sub_self _).trans (mul_zero _).symm

/-- The map `x ↦ x - 1` is good. -/
theorem sub_one_is_good [Ring R] : good (· - (1 : R)) := λ x y ↦ by
  rw [sub_sub_sub_cancel_right, ← sub_sub_sub_eq, ← mul_sub_one, sub_one_mul]

/-- The map `x ↦ x^2 - 1` is good if `R` is commutative. -/
theorem sq_sub_one_is_good [CommRing R] : good (· ^ 2 - (1 : R)) :=
  λ x y ↦ by ring

variable [Ring R]

/-- The map `𝔽₂_map` is good. -/
theorem 𝔽₂Map_is_good : good (𝔽₂Map R)
  | 0, _ => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm

/-- The map `𝔽₃_map1` is good. -/
theorem 𝔽₃Map1_is_good : good (𝔽₃Map1 R)
  | 0, _ => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm
  | 2, 0 => (zero_sub _).trans (mul_neg_one _).symm
  | 2, 1 => (sub_self _).trans (mul_zero _).symm
  | 2, 2 => (sub_zero _).trans (mul_one _).symm

/-- The map `𝔽₃_map2` is good. -/
theorem 𝔽₃Map2_is_good : good (𝔽₃Map2 R)
  | 0, _ => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm
  | 2, 0 => (sub_self _).trans (zero_mul _).symm
  | 2, 1 => (sub_self _).trans (mul_zero _).symm
  | 2, 2 => (sub_zero _).trans (mul_zero _).symm

/-- The map `ℤ₄_map` is good. -/
theorem ℤ₄Map_is_good : good (ℤ₄Map R)
  | 0, _ => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm
  | x, 0 => by rw [mul_zero, add_zero]
               exact (zero_sub _).trans (mul_neg_one _).symm
  | x, 1 => (mul_one x).symm ▸ (sub_self _).trans (mul_zero _).symm
  | 2, 2 => (zero_sub _).trans <| (neg_neg _).trans (mul_one _).symm
  | 2, 3 => (sub_self _).trans (mul_zero _).symm
  | 3, 2 => (sub_self _).trans (zero_mul _).symm
  | 3, 3 => (sub_self _).trans (zero_mul _).symm

/-- The map `𝔽₂ε_map` is good. -/
theorem 𝔽₂εMap_is_good : good (𝔽₂εMap R)
  | 0, x => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm
  | x, 0 => by rw [mul_zero, add_zero]
               exact (zero_sub _).trans (mul_neg_one _).symm
  | x, 1 => (mul_one x).symm ▸ (sub_self _).trans (mul_zero _).symm
  | 𝔽₂ε.X, 𝔽₂ε.X => (zero_sub _).trans <| (neg_neg _).trans (one_mul _).symm
  | 𝔽₂ε.X, 𝔽₂ε.Y => (sub_self _).trans (one_mul _).symm
  | 𝔽₂ε.Y, 𝔽₂ε.X => (sub_self _).trans (zero_mul _).symm
  | 𝔽₂ε.Y, 𝔽₂ε.Y => (sub_self _).trans (zero_mul _).symm

/-- The map `𝔽₄_map` is good. -/
theorem 𝔽₄Map_is_good (h : c * (1 - c) = -1) : good (𝔽₄Map R c)
  | 0, x => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm
  | x, 0 => by rw [mul_zero, add_zero]
               exact (zero_sub _).trans (mul_neg_one _).symm
  | x, 1 => (mul_one x).symm ▸ (sub_self _).trans (mul_zero _).symm
  | 𝔽₄.X, 𝔽₄.X => by change c - -1 = c * c
                     rw [← h, ← mul_one_sub, sub_sub_cancel]
  | 𝔽₄.X, 𝔽₄.Y => (sub_zero _).trans h.symm
  | 𝔽₄.Y, 𝔽₄.X => by change (-1) - 0 = (1 - c) * c
                     rw [sub_zero (-1), ← h, mul_one_sub, ← one_sub_mul]
  | 𝔽₄.Y, 𝔽₄.Y => by change (1 - c) - -1 = (1 - c) * (1 - c)
                     rw [one_sub_mul, h]



theorem good_map_comp_hom [Ring R₀] [Ring S]
    {f : R → S} (h : good f) (φ : R₀ →+* R) : good (f ∘ φ) := λ x y ↦
  h (φ x) (φ y) ▸ congr_arg₂ (λ u v ↦ f u - f v)
    (by rw [φ.map_add, φ.map_mul, φ.map_one]) (φ.map_add x y)

theorem good_of_IsAnswer [CommRing S] {f : R → S} (h : IsAnswer f) : good f :=
  h.recOn zero_is_good
    (good_map_comp_hom sub_one_is_good)
    (good_map_comp_hom sq_sub_one_is_good)
    (λ φ _ ↦ good_map_comp_hom 𝔽₂Map_is_good φ)
    (λ φ _ ↦ good_map_comp_hom 𝔽₃Map1_is_good φ)
    (λ φ _ ↦ good_map_comp_hom 𝔽₃Map2_is_good φ)
    (λ φ _ ↦ good_map_comp_hom ℤ₄Map_is_good φ)
    (λ φ _ ↦ good_map_comp_hom 𝔽₂εMap_is_good φ)
    (λ φ _ _ h ↦ good_map_comp_hom (𝔽₄Map_is_good h) φ)
