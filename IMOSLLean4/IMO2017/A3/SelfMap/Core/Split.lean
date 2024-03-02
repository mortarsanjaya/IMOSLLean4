/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.SplitMap.Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Core.Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Equiv.Defs

/-!
# Splitting of self-maps with respect to a core

Let `Y` be a core of `f` with projection `φ` and inclusion `ι`.
We say that the core *splits* if `ι ∘ Y.f ∘ φ = X.f`.
If the core splits, then `X` is isomorphic to a split map with core `Y`.
The section is defined by restricting `φ` on `α ∖ ι(β)`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace Core

def splits (C : Core X Y) := C.ι ∘ Y.f ∘ C.φ = X.f



variable {X : SelfMap.{u}} (C : Core X Y)

abbrev split_section : Y.α ⊕ {a // ¬∃ b, C.ι b = a} → X.α :=
  Sum.elim C.ι Subtype.val

lemma split_section_injective : (split_section C).Injective
  | Sum.inl _, Sum.inl _ => λ h ↦ congr_arg Sum.inl (C.ι_injective h)
  | Sum.inl b, Sum.inr a => λ h ↦ a.2.elim ⟨b, h⟩
  | Sum.inr a, Sum.inl b => λ h ↦ a.2.elim ⟨b, h.symm⟩
  | Sum.inr _, Sum.inr _ => λ h ↦ congr_arg Sum.inr (Subtype.eq h)

lemma split_section_surjective : (split_section C).Surjective :=
  λ a ↦ (em (∃ b, C.ι b = a)).elim
    (λ h ↦ h.elim λ b h ↦ ⟨Sum.inl b, h⟩)
    (λ h ↦ ⟨Sum.inr ⟨a, h⟩, rfl⟩)

lemma split_section_bijective : (split_section C).Bijective :=
  ⟨split_section_injective C, split_section_surjective C⟩

noncomputable def toSplitMapEquiv (h : splits C) :
    Equiv (SplitMap Y λ x : {a // ¬∃ b, C.ι b = a} ↦ C.φ x.1) X where
  toEquiv := Equiv.ofBijective _ (split_section_bijective C)
  Semiconj := λ x ↦ match x with
    | Sum.inl _ => C.ι.Semiconj _
    | Sum.inr ⟨_, _⟩ => congr_fun h _

/-- Noempty instance of isomorphism to a split map -/
lemma Nonempty_SplitMapEquiv_of_splits (h : splits C) :
    ∃ (β : Type u) (s : β → Y.α), Nonempty (Equiv (SplitMap Y s) X) :=
  ⟨_, _, ⟨toSplitMapEquiv C h⟩⟩
