/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.A3Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Core.Defs

/-!
# IMO 2017 A3 (Good self-maps and core)

We prove that the core of a good self-map is a good self-map.
-/

namespace IMOSL
namespace IMO2017A3

variable {X Y : SelfMap}

lemma bad_pair_of_core (C : X.Core Y) (h : bad_pair Y.f g) :
    bad_pair X.f (C.ι ∘ g ∘ C.φ) := funext λ x ↦ by
  simp only [Function.comp_apply]
  rw [← C.ι.Semiconj, C.φ.Semiconj, C.φ.Semiconj, C.is_inv]
  exact congr_arg _ (congr_fun h _)

lemma good_of_core (C : X.Core Y) (h : good X) : good Y := λ g h0 ↦ by
  change id ∘ g ∘ id = Y.f
  rw [← C.half_conj, ← C.φ_comp_ι]
  exact congr_arg (λ s ↦ C.φ ∘ s ∘ C.ι) (h _ (bad_pair_of_core C h0))
