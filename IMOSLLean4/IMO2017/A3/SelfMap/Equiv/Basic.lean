/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Equiv.Defs
import Mathlib.Logic.Equiv.Basic

/-!
# More isomorphisms between self-maps

This file constructs more isomorphisms of self-maps.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace Equiv

/-- Binary sums of isomorphisms -/
def sum_map (e₁ : Equiv X₁ Y₁) (e₂ : Equiv X₂ Y₂) :
    Equiv (sum X₁ X₂) (sum Y₁ Y₂) where
  toEquiv := _root_.Equiv.sumCongr e₁.toEquiv e₂.toEquiv
  Semiconj := (Hom.sum_map e₁.toHom e₂.toHom).Semiconj

/-- Isomorphism to direct sum of fibers -/
def sigma_fiber (s : I → J) (X : J → SelfMap) :
    Equiv (sigma λ p : (j : J) × {i // s i = j} ↦ X p.1) (sigma (X ∘ s)) :=
  sigma_map (Equiv.sigmaFiberEquiv s) (λ ⟨j, i, h⟩ ↦ h ▸ refl (X _))
