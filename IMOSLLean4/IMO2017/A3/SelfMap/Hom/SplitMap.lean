/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Equiv

/-!
# Splitting of self-maps with respect to core

Let `f : α → α` and `s : β → α` be functions.
The *split map* of `f` with section `s`, defined by `SplitMap f s`,
  is the map defined by `ι ∘ f ∘ (id ⊕ s)`, where `id ⊕ s` is the
  coproduct of `id` and `s`, and `ι : β → β ⊕ γ` is the inclusion.
We give `SplitMap f s` a canonical core instance of `f`.

Let `f : α → α` be a self-map with a core `g : β → β`.
Let `φ : α → β` and `ι : β → α` be the underlying homomorphisms.
We show that if `ι ∘ g ∘ φ = f`, then `f` is isomorphic to a
  split map of `g`, where the section is defined by `φ` on `α ∖ ι(β)`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

def SplitMap (f : α → α) (s : β → α) : α ⊕ β → α ⊕ β :=
  Sum.inl ∘ f ∘ (Sum.elim id s)


namespace SplitMap

variable (f : α → α) (s : β → α)

lemma apply_inl (a : α) : SplitMap f s (Sum.inl a) = Sum.inl (f a) := rfl

lemma apply_inr (b : β) : SplitMap f s (Sum.inr b) = Sum.inl (f (s b)) := rfl





/-! ### Canonical core of a split map -/

def toCoreHom : Hom (SplitMap f s) f :=
  ⟨Sum.elim id s, λ _ ↦ rfl⟩

def fromCoreHom : Hom f (SplitMap f s) :=
  ⟨Sum.inl, λ _ ↦ rfl⟩

def toCore : Core (SplitMap f s) f :=
  ⟨toCoreHom f s, fromCoreHom f s, λ _ ↦ rfl⟩

end SplitMap





/-! ### Split map from a core structure -/

namespace Core

open scoped Classical

variable {f : α → α} {g : β → β} (C : Core f g)

abbrev SplitMapType := β ⊕ {a // ¬∃ b, C.ι b = a}

abbrev SplitMapType_fn : SplitMapType C → α :=
  Sum.elim C.ι Subtype.val

lemma SplitMapType_fn_injective : (SplitMapType_fn C).Injective
  | Sum.inl _, Sum.inl _ => λ h ↦ congr_arg Sum.inl (C.ι_injective h)
  | Sum.inl b, Sum.inr a => λ h ↦ a.2.elim ⟨b, h⟩
  | Sum.inr a, Sum.inl b => λ h ↦ a.2.elim ⟨b, h.symm⟩
  | Sum.inr _, Sum.inr _ => λ h ↦ congr_arg Sum.inr (Subtype.eq h)

lemma SplitMapType_fn_surjective : (SplitMapType_fn C).Surjective :=
  λ a ↦ (em (∃ b, C.ι b = a)).elim
    (λ h ↦ h.elim λ b h ↦ ⟨Sum.inl b, h⟩)
    (λ h ↦ ⟨Sum.inr ⟨a, h⟩, rfl⟩)

lemma SplitMapType_fn_bijective : (SplitMapType_fn C).Bijective :=
  ⟨SplitMapType_fn_injective C, SplitMapType_fn_surjective C⟩

noncomputable def SplitMapTypeEquiv : SplitMapType C ≃ α :=
  Equiv.ofBijective _ (SplitMapType_fn_bijective C)

/-- Split map from core -/
def toSplitMap : SplitMapType C → SplitMapType C :=
  SplitMap g (λ x ↦ C.φ x.1)

noncomputable def toSplitMapEquiv (h : C.ι ∘ g ∘ C.φ = f) :
    SelfMap.Equiv (toSplitMap C) f where
  toEquiv := SplitMapTypeEquiv C
  Semiconj := λ x ↦ match x with
    | Sum.inl _ => C.ι.Semiconj _
    | Sum.inr ⟨_, _⟩ => congr_fun h _

end Core
