/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5Defs
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# IMO 2012 A5 (Good maps and ring homomorphisms)

We prove some results relating good maps and ring homomorphisms.
Namely, good maps behave well with respect to composing with ring homomorphisms.
-/

namespace IMOSL
namespace IMO2012A5

variable [NonAssocSemiring R] [NonAssocRing S] {f : R → S}

theorem good_comp_hom (h : good f) [NonAssocRing R₀]
    (φ : R₀ →+* R) : good (f ∘ φ) := λ x y ↦ by
  simp only [Function.comp_apply]
  rw [φ.map_add, φ.map_mul, φ.map_one, h, φ.map_add]

theorem good_hom_comp (h : good f) [NonAssocRing S₀]
    (φ : S →+* S₀) : good (φ ∘ f) := λ x y ↦ by
  simp only [Function.comp_apply]
  rw [h, φ.map_add, φ.map_mul]

theorem NontrivialGood.comp_hom (hf : NontrivialGood f) [NonAssocRing R₀]
    (φ : R₀ →+* R) : NontrivialGood (f ∘ φ) :=
  ⟨good_comp_hom hf.is_good φ, hf.map_one ▸ congrArg f φ.map_one,
    hf.map_zero_add_one ▸ congrArg (λ x ↦ f x + 1) φ.map_zero⟩

theorem NontrivialGood.hom_comp (hf : NontrivialGood f) [NonAssocRing S₀]
    (φ : S →+* S₀) : NontrivialGood (φ ∘ f) :=
  ⟨good_hom_comp hf.is_good φ, φ.map_zero ▸ φ.congr_arg hf.map_one,
    by rw [← φ.map_one, ← φ.map_zero, ← hf.map_zero_add_one, φ.map_add]; rfl⟩
