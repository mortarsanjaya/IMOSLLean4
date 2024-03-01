/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Core.Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Equiv.Defs

/-!
# Splitting of self-maps with respect to core

Let `X` be a self-map and `s : β → X.α` be a function.
The *split map* with core `X` and section `s` is the self-map on
  `X.α ⊕ β` defined by `X.f` on `X.α` and `X.f ∘ s` on `β`.
As the description implies, `X` is a core of the split map.

Let `Y` be a core of `f` with underlying homomorphism `φ : X.α → Y.α` and `ι`.
We say that the core *splits* if `ι ∘ Y.f ∘ φ = X.f`.
If the core splits, then `X` is isomorphic to a split map with core `Y`.
The section is defined by `φ` on `α ∖ ι(β)`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

def splits (C : Core X Y) := C.ι ∘ Y.f ∘ C.φ = X.f

def SplitMap (X : SelfMap) (s : β → X.α) : SelfMap :=
  ⟨X.α ⊕ β, Sum.inl ∘ X.f ∘ Sum.elim id s⟩



namespace SplitMap

variable (X : SelfMap) (s : β → X.α)

lemma apply_inl (a : X.α) :
    (SplitMap X s).f (Sum.inl a) = Sum.inl (X.f a) := rfl

lemma apply_inr (b : β) :
    (SplitMap X s).f (Sum.inr b) = Sum.inl (X.f (s b)) := rfl



/-! ### Canonical core of a split map -/

def toCoreHom : Hom (SplitMap X s) X :=
  ⟨Sum.elim id s, λ _ ↦ rfl⟩

def fromCoreHom : Hom X (SplitMap X s) :=
  ⟨Sum.inl, λ _ ↦ rfl⟩

def toCore : Core (SplitMap X s) X :=
  ⟨toCoreHom X s, fromCoreHom X s, λ _ ↦ rfl⟩

end SplitMap





/-! ### Split map from a core structure -/

namespace Core

open scoped Classical

variable {X : SelfMap.{u}} (C : Core X Y)

abbrev SplitMapType_fn : Y.α ⊕ {a // ¬∃ b, C.ι b = a} → X.α :=
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

noncomputable def SplitMapTypeEquiv : Y.α ⊕ {a // ¬∃ b, C.ι b = a} ≃ X.α :=
  Equiv.ofBijective _ (SplitMapType_fn_bijective C)

/-- Split map from core -/
def toSplitMap : SelfMap := SplitMap Y λ x : {a // ¬∃ b, C.ι b = a} ↦ C.φ x.1

noncomputable def toSplitMapEquiv (h : splits C) : Equiv (toSplitMap C) X where
  toEquiv := SplitMapTypeEquiv C
  Semiconj := λ x ↦ match x with
    | Sum.inl _ => C.ι.Semiconj _
    | Sum.inr ⟨_, _⟩ => congr_fun h _

/-- Noempty instance of split map -/
lemma Nonempty_SplitMapEquiv_of_splits (h : splits C) :
    ∃ (β : Type u) (s : β → Y.α), Nonempty (Equiv (SplitMap Y s) X) :=
  ⟨_, _, ⟨toSplitMapEquiv C h⟩⟩

end Core
