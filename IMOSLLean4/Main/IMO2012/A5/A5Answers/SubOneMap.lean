/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.A5.A5Defs
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# IMO 2012 A5 (`x ↦ x - 1`)

We show that the map `x : R ↦ x - 1` on a ring `R` is a good map.
Then we implement the `f(x + 1) = f(x) + 1` solver.
-/

namespace IMOSL
namespace IMO2012A5

variable [NonAssocRing R]

theorem sub_one_is_good : good (λ (x : R) ↦ x - 1) := λ x y ↦ by
  rw [sub_one_mul, mul_sub_one, sub_sub, ← add_sub_assoc x, sub_add_cancel]
  exact add_sub_cancel_right _ _

theorem sub_one_is_NontrivialGood : NontrivialGood (λ (x : R) ↦ x - 1) :=
  ⟨sub_one_is_good, sub_add_cancel 0 1⟩

theorem sub_one_solver [NonAssocRing S] {f : R → S} (hf : NontrivialGood f)
    (h : ∀ x, f (x + 1) = f x + 1) : ∃ φ : R →+* S, ∀ x, f x = φ (x - 1) := by
  ---- Reduce to showing `f(x + y) = f(x) + f(y) + 1` for all `x y : R`
  suffices ∀ x y, f (x + y) = f x + f y + 1 by
    have h0 (x y) : f (x + y + 1) = f (x + 1) + f (y + 1) := by
      rw [h, h, h, this, add_assoc, add_add_add_comm]
    have h1 (x y) : f (x * y + 1) = f (x + 1) * f (y + 1) := by
      rw [hf.is_good, h, h, this, add_assoc, ← add_assoc,
        ← mul_add_one (f x), ← add_one_mul (f x)]
    exact ⟨⟨⟨⟨λ x ↦ f (x + 1), (h 1).trans <| by rw [hf.map_one, zero_add]⟩, h1⟩,
        ((h 0).trans hf.map_zero_add_one), h0⟩,
      λ x ↦ congrArg f (sub_add_cancel x 1).symm⟩
  ---- Collect some results
  have h0 (x y) : f (x * y) + 1 = f x * f y + f (x + y) :=
    (h _).symm.trans (hf.is_good x y)
  have h1 (x y) : f (x * y) = f x * f y + f (x + y) - 1 :=
    eq_sub_of_add_eq (h0 x y)
  have h2 (x y) : f ((x + 1) * y) = f (x * y) + (f y + 1) := by
    rw [h1, h, add_right_comm, add_one_mul (f x), h, add_add_add_comm,
      ← h0, add_right_comm, add_sub_cancel_right]
  ---- Decompose `f(x(x + 1) y)` in two ways
  intro x y
  have h3 : f (x * ((x + 1) * y)) = f ((x + 1) * (x * y)) := by
    rw [add_one_mul x, add_one_mul x, mul_add]
  ---- Pure bash (TODO: Optimize if possible)
  rwa [h2, h1, h2, mul_add, ← add_assoc, add_right_comm _ _ 1, h0, ← h,
    sub_eq_iff_eq_add, add_assoc, add_assoc, add_assoc, add_right_inj,
    ← add_left_inj 1, add_assoc, ← h, add_right_comm, ← mul_one_add (x + 1),
    h2, add_left_comm, mul_one_add x, add_assoc, add_right_inj, add_comm 1,
    h, mul_add_one (f x), h0, add_assoc, add_assoc (_ * _), add_right_inj,
    ← add_assoc, add_left_inj, ← add_assoc, eq_comm] at h3
