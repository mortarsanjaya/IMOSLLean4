/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.CharTwo.Defs
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Characteristic two monoids and homomorphisms

We prove some results relating characteristic two monoids and homomorphism.
-/

namespace IMOSL
namespace Extra
namespace CharTwo

variable [AddMonoid R] [CharTwo R] [AddMonoid R']

theorem pullback_of_inj (φ : R' →+ R) (h : Function.Injective φ) : CharTwo R' :=
  ⟨λ x ↦ h <| by rw [φ.map_add, φ.map_zero, CharTwo.add_self_eq_zero]⟩

theorem forward_of_surj (φ : R →+ R') (h : Function.Surjective φ) : CharTwo R' :=
  ⟨λ x ↦ (h x).elim λ c h0 ↦ by rw [← h0, ← φ.map_add, add_self_eq_zero, φ.map_zero]⟩
