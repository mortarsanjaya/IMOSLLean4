/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom
import Mathlib.Logic.Equiv.Defs

/-!
# Isomorphisms between self-maps

An isomorphism between two self-maps is a bijective homomorphism.
The inverse is also automatically a homomorphism of self-maps.
Definitions requiring more imports are given in `SelfMap/Equiv/Basic.lean`,
  notably those requiring `Mathlib/Logic/Equiv/Basic`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

structure Equiv (X Y : SelfMap) extends X.α ≃ Y.α, Hom X Y



namespace Equiv

def of_conj {e : X.α ≃ Y.α} (h : e.conj X.f = Y.f) : Equiv X Y :=
  ⟨e, Function.semiconj_iff_comp_eq.mpr <| (e.comp_symm_eq _ _).mp h⟩

lemma right_eq_conj (e : Equiv X Y) : e.conj X.f = Y.f :=
  (e.comp_symm_eq _ _).mpr e.Semiconj.comp_eq

def refl (X : SelfMap) : Equiv X X := ⟨_root_.Equiv.refl _, λ _ ↦ rfl⟩

def symm (e : Equiv X Y) : Equiv Y X :=
  of_conj (e.conj.symm_apply_eq.mpr e.right_eq_conj.symm)

def trans (e₁ : Equiv X Y) (e₂ : Equiv Y Z) : Equiv X Z where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  Semiconj := (e₂.toHom.comp e₁.toHom).Semiconj



/-! ##### Sigma -/

def sigma_map (e : I ≃ J) (E : (i : I) → Equiv (X i) (Y (e i))) :
    Equiv (sigma X) (sigma Y) where
  toEquiv := _root_.Equiv.sigmaCongr e λ i ↦ (E i).toEquiv
  Semiconj := λ ⟨i, x⟩ ↦ Sigma.ext rfl <| heq_of_eq ((E i).Semiconj x)

def sigma_map_id (E : (i : I) → Equiv (X i) (Y i)) :
    Equiv (sigma X) (sigma Y) :=
  sigma_map (_root_.Equiv.refl I) E
