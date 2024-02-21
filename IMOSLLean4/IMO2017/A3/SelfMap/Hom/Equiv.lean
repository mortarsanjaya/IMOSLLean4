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
We show that the inverse is automatically a homomorphism of self-maps.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

structure Equiv (f : α → α) (g : β → β) extends α ≃ β, Hom f g


namespace Equiv

def of_conj {e : α ≃ β} (h : e.conj f = g) : Equiv f g :=
  ⟨e, Function.semiconj_iff_comp_eq.mpr <| (e.comp_symm_eq _ _).mp h⟩

lemma right_eq_conj (e : Equiv f g) : e.conj f = g :=
  (e.comp_symm_eq _ _).mpr e.Semiconj.comp_eq

def symm (e : Equiv f g) : Equiv g f :=
  of_conj (e.conj.symm_apply_eq.mpr e.right_eq_conj.symm)

def trans (e₁ : Equiv f g) (e₂ : Equiv g h) : Equiv f h where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  Semiconj := (e₂.toHom.comp e₁.toHom).Semiconj

def toCore (e : Equiv f g) : Core f g :=
  ⟨e.toHom, e.symm.toHom, e.right_inv⟩
