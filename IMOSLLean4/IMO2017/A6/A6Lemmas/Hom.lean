/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Defs
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# IMO 2017 A6 (P2, Good functions and homomorphism)

Let `φ : R → S` be a homomorphism of rings.
Suppose that `φ` has a right inverse `ι : S → R` that is a group homomorphism.
Then for any `f : S → S`, `ι ∘ f ∘ φ` is a good function iff `f` is a good function.
-/

namespace IMOSL
namespace IMO2017A6
namespace good

open Function

variable [Ring R] [Ring S] (φ : R →+* S) (ι : S →+ R) (h : LeftInverse φ ι) {f : S → S}
include h

theorem to_hom_pair (hf : good f) : good (ι ∘ f ∘ φ) := λ x y ↦ by
  simp only [comp_apply]
  rw [φ.map_mul, h, h, φ.map_add, φ.map_mul, ← ι.map_add]
  exact congrArg _ (hf (φ x) (φ y))

theorem of_hom_pair (hf : good (ι ∘ f ∘ φ)) : good f := λ x y ↦ by
  specialize hf (ι x) (ι y); simp only [comp_apply] at hf
  rw [h, h, φ.map_mul, φ.map_add, φ.map_mul, h, h, h, h, ← ι.map_add] at hf
  exact h.injective hf

theorem iff_hom_pair : good (ι ∘ f ∘ φ) ↔ good f :=
  ⟨of_hom_pair φ ι h, to_hom_pair φ ι h⟩
