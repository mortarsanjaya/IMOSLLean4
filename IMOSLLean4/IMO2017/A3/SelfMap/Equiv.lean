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
We show that the inverse is automatically a homomorphism of self-maps.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

structure Equiv (X Y : SelfMap) extends X.α ≃ Y.α, Hom X Y



namespace Equiv

variable {X Y : SelfMap}

def of_conj {e : X.α ≃ Y.α} (h : e.conj X.f = Y.f) : Equiv X Y :=
  ⟨e, Function.semiconj_iff_comp_eq.mpr <| (e.comp_symm_eq _ _).mp h⟩

lemma right_eq_conj (e : Equiv X Y) : e.conj X.f = Y.f :=
  (e.comp_symm_eq _ _).mpr e.Semiconj.comp_eq

def symm (e : Equiv X Y) : Equiv Y X :=
  of_conj (e.conj.symm_apply_eq.mpr e.right_eq_conj.symm)

def trans (e₁ : Equiv X Y) (e₂ : Equiv Y Z) : Equiv X Z where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  Semiconj := (e₂.toHom.comp e₁.toHom).Semiconj
