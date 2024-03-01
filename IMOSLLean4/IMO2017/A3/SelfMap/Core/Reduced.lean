/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Core.Equiv
import IMOSLLean4.IMO2017.A3.SelfMap.Equiv.Basic

/-!
# Reduced core of self-maps

Let `X(i)` be a family of `I`-indexed self-maps and `s : J → I` be a function.
We show that if `s` is surjective, then `Σ X` is a core of `Σ_J X(s(j))`.
For general `s`, then instead `Σ_{s(J)} X` is a core of `Σ_J X(s(j))`.
We call these the reduction of `Σ_J X(s(j))`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace Core

variable {I : Type*} (X : I → SelfMap)

def sigma_inv_reduction {s : J → I} (h : s.LeftInverse t) :
    Core (sigma λ j : J ↦ X (s j)) (sigma X) :=
  (ofEquiv (Equiv.sigma_fiber _ _).symm).trans
    (sigma_sigma_reduction X λ i ↦ ⟨t i, h i⟩)

noncomputable def sigma_surjective_reduction {s : J → I} (h : s.Surjective) :
    Core (sigma λ j : J ↦ X (s j)) (sigma X) :=
  sigma_inv_reduction X (Function.surjInv_eq h)

noncomputable def sigma_subtype_reduction (s : J → I) :
    Core (sigma λ j : J ↦ X (s j)) (sigma λ i : {i // ∃ j, s j = i} ↦ X i.1) :=
  sigma_surjective_reduction (λ i : {i // ∃ j, s j = i} ↦ X i.1)
    (s := λ j ↦ ⟨s j, j, rfl⟩) (λ i ↦ i.2.elim λ j h ↦ ⟨j, Subtype.ext h⟩)
