/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.A3Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Equiv

/-!
# IMO 2017 A3 (Good maps and isomorphism)

We prove that if `f` is good and `g` is a core of `f`, then `g` is good.
As an implication, if `f` and `g` are isomorphic, then
  `f` is good if and only if `g` is good.
-/

namespace IMOSL
namespace IMO2017A3

lemma bad_pair_of_core (C : SelfMap.Core f g) (h : bad_pair g g') :
    bad_pair f (C.ι ∘ g' ∘ C.φ) := funext λ x ↦ by
  simp only [Function.comp_apply]
  rw [← C.ι.Semiconj, C.φ.Semiconj, C.φ.Semiconj, C.is_inv]
  exact congr_arg _ (congr_fun h _)

lemma good_of_core (C : SelfMap.Core f g) (h : good f) : good g := λ g' h0 ↦ by
  change id ∘ g' ∘ id = g
  rw [← C.half_conj, ← C.φ_comp_ι]
  exact congr_arg (λ s ↦ C.φ ∘ s ∘ C.ι) (h _ (bad_pair_of_core C h0))

lemma good_of_equiv (e : SelfMap.Equiv f g) (h : good f) : good g :=
  good_of_core e.toCore h

lemma good_iff_equiv (e : SelfMap.Equiv f g) : good f ↔ good g :=
  ⟨good_of_equiv e, good_of_equiv e.symm⟩
