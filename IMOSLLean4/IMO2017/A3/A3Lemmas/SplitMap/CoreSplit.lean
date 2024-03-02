/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.A3Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Core.Split

/-!
# IMO 2017 A3 (Good maps and splitting of core structures)

This file proves results relating core structures and good maps.
We prove a nice characterization of good split maps, and we prove when
  the sum of two split maps is a good map in terms of the components.
-/

namespace IMOSL
namespace IMO2017A3

variable {X : SelfMap.{u}} (C : X.Core Y)

lemma bad_pair_of_core (h : bad_pair Y.f g) :
    bad_pair X.f (C.ι ∘ g ∘ C.φ) := funext λ x ↦ by
  simp only [Function.comp_apply]
  rw [← C.ι.Semiconj, C.φ.Semiconj, C.φ.Semiconj, C.is_inv]
  exact congr_arg _ (congr_fun h _)

variable (h : good X)

lemma good_of_core : good Y := λ g h0 ↦ by
  change id ∘ g ∘ id = Y.f
  rw [← C.half_conj, ← C.φ_comp_ι]
  exact congr_arg (λ s ↦ C.φ ∘ s ∘ C.ι) (h _ (bad_pair_of_core C h0))

lemma good_core_splits : C.splits :=
  h _ (bad_pair_of_core C rfl)

lemma good_core_exists_SplitMapEquiv :
    ∃ (β : Type u) (s : β → Y.α), Nonempty ((Y.SplitMap s).Equiv X) :=
  C.Nonempty_SplitMapEquiv_of_splits (good_core_splits C h)
