/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic

/-!
# Homomorphism and sums

We construct homomorphisms and cores related to sums.
* Given self-maps `f` and `g`, we construct
    homomorphisms from `f` and `g` to `f ⊕ g`.
* Given self-map homomorphisms from `f₁` and `f₂` to `g`,
    we construct a homomorphism from `f₁ ⊕ f₂` to `g`.
* Given a core `f` over `g₁` and a homomorphism `f → g₂`,
    we construct a core instance of `f` over `g₁ ⊕ g₂`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

namespace Hom

def sum_inl (f : α → α) (g : β → β) : Hom f (Sum.map f g) :=
  ⟨Sum.inl, λ _ ↦ rfl⟩

def sum_inr (f : α → α) (g : β → β) : Hom g (Sum.map f g) :=
  ⟨Sum.inr, λ _ ↦ rfl⟩

def sum_elim (e₁ : Hom f₁ g) (e₂ : Hom f₂ g) : Hom (Sum.map f₁ f₂) g :=
  ⟨Sum.elim e₁ e₂, λ x ↦ match x with
    | Sum.inl x => e₁.Semiconj x
    | Sum.inr x => e₂.Semiconj x⟩

end Hom



namespace Core

def sum_Hom (C : Core f g) (e : Hom h g) : Core (Sum.map f h) g where
  φ := C.φ.sum_elim e
  ι := (Hom.sum_inl f h).comp C.ι
  is_inv := C.is_inv

end Core
