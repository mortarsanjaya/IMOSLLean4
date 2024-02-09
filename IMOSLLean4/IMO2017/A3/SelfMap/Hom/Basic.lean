/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Logic.Function.Conjugate

/-!
# Homomorphisms between self-maps

Let `f : α → α` and `g : β → β` be self-maps.
A homomorphism from `f` to `g` is a function `e : α → β` that
  semiconjugates `f` to `g`, i.e., satisfies `e ∘ f = g ∘ e`.
-/

namespace IMOSL
namespace IMO2017A3

/-- Homomorphisms between self-maps -/
structure SelfMapHom (f : α → α) (g : β → β) where
  toFun : α → β
  Semiconj : toFun.Semiconj f g



namespace SelfMapHom

def id (f : α → α) : SelfMapHom f f :=
  ⟨λ x ↦ x, Function.Semiconj.id_left⟩

def comp (e₁ : SelfMapHom g h) (e₂ : SelfMapHom f g) : SelfMapHom f h :=
  ⟨e₁.toFun ∘ e₂.toFun, e₁.Semiconj.comp_left e₂.Semiconj⟩

theorem id_comp (e : SelfMapHom f g) : (id g).comp e = e := rfl

theorem comp_id (e : SelfMapHom f g) : e.comp (id f) = e := rfl

theorem comp_assoc
    (e₁ : SelfMapHom g h) (e₂ : SelfMapHom f g) (e₃ : SelfMapHom s f) :
    (e₁.comp e₂).comp e₃ = e₁.comp (e₂.comp e₃) := rfl
