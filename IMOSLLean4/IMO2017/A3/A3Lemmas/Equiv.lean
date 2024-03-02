/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.A3Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Equiv.Defs

/-!
# IMO 2017 A3 (Good self-maps and isomorphism)

We prove that the `good` predicate respects isomorphism of self-maps.
-/

namespace IMOSL
namespace IMO2017A3

lemma bad_pair_conj (e : α ≃ β) {f g : α → α} (h : bad_pair f g) :
    bad_pair (e.conj f) (e.conj g) := by
  rw [bad_pair]
  iterate 4 rw [← e.conj_comp]
  exact congr_arg _ h


variable {X Y : SelfMap} (e : X.Equiv Y)

lemma good_of_equiv (h : good X) : good Y := λ g h0 ↦ by
  specialize h (e.symm.conj g)
  rw [← e.symm.right_eq_conj] at h
  exact e.symm.conj.injective (h (bad_pair_conj _ h0))

lemma good_iff_equiv : good X ↔ good Y :=
  ⟨good_of_equiv e, good_of_equiv e.symm⟩
