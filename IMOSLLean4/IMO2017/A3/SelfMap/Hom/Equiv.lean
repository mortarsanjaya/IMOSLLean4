/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Isomorphisms between self-maps

An isomorphism between two self-maps is a bijective homomorphism.
We show that the inverse is also a homomorphism of self-maps.
This justifies the definition.
-/

namespace IMOSL
namespace IMO2017A3

structure SelfMapEquiv (f : α → α) (g : β → β) extends α ≃ β, SelfMapHom f g



namespace SelfMapEquiv

def of_conj {e : α ≃ β} (h : e.conj f = g) : SelfMapEquiv f g :=
  ⟨e, Function.semiconj_iff_comp_eq.mpr <| (e.comp_symm_eq _ _).mp h⟩

lemma right_eq_conj (e : SelfMapEquiv f g) : e.conj f = g :=
  (e.comp_symm_eq _ _).mpr e.Semiconj.comp_eq

def symm (e : SelfMapEquiv f g) : SelfMapEquiv g f :=
  of_conj (e.conj.symm_apply_eq.mpr e.right_eq_conj.symm)
