/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Homomorphisms between self-maps

Let `f : α → α` and `g : β → β` be self-maps.
A homomorphism from `f` to `g` is a function `e : α → β` that
  semiconjugates `f` to `g`, i.e., satisfies `e ∘ f = g ∘ e`.
We also give one more definition:
* Given `f : α → α` and `g : β → β`, we say that `g` is a core of `f`,
  denoted `Core f g`, if there exists homomorphisms `e : f → g` and
  `ι : g → f` such that `e ∘ ι = id_β`. A core should be thought of
  as a homomorphically equivalent subgraph. Note that unlike in the
  case of graphs, a core does not have to be minimal.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

/-- Homomorphisms between self-maps -/
structure Hom (f : α → α) (g : β → β) where
  toFun : α → β
  Semiconj : toFun.Semiconj f g


namespace Hom

instance (f : α → α) (g : β → β) : FunLike (Hom f g) α β :=
  ⟨toFun, λ e₁ e₂ h ↦ by cases e₁; cases e₂; congr⟩

instance (f : α → α) (g : β → β) : CoeFun (Hom f g) (λ _ ↦ α → β) := ⟨toFun⟩

@[ext] theorem ext {e₁ e₂ : Hom f g} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
  DFunLike.ext e₁ e₂ h

theorem ext_iff {e₁ e₂ : Hom f g} : (∀ x, e₁ x = e₂ x) ↔ e₁ = e₂ :=
  ⟨ext, λ h _ ↦ h ▸ rfl⟩

/-- Copy of a `MyHom` with a new `toFun` equal to the old one.
  Useful to fix definitional equalities. -/
protected def copy (e : Hom f g) (e') (h : e' = ⇑e) : Hom f g :=
  ⟨e', h ▸ e.Semiconj⟩



def id (f : α → α) : Hom f f :=
  ⟨λ x ↦ x, Function.Semiconj.id_left⟩

def comp (φ₁ : Hom g h) (φ₂ : Hom f g) : Hom f h :=
  ⟨φ₁ ∘ φ₂, φ₁.Semiconj.comp_left φ₂.Semiconj⟩

theorem id_comp (φ : Hom f g) : (id g).comp φ = φ := rfl

theorem comp_id (φ : Hom f g) : φ.comp (id f) = φ := rfl

theorem comp_assoc (φ₁ : Hom f₂ f₃) (φ₂ : Hom f₁ f₂) (φ₃ : Hom f₀ f₁) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) := rfl


lemma semiconj (φ : Hom f g) : φ ∘ f = g ∘ φ :=
  funext φ.Semiconj

lemma semiconj_apply (φ : Hom f g) (x) : φ (f x) = g (φ x) :=
  φ.Semiconj x

lemma semiconj_iterate (φ : Hom f g) (k : ℕ) : φ ∘ f^[k] = g^[k] ∘ φ :=
  funext (φ.Semiconj.iterate_right k)

lemma semiconj_iterate_apply (φ : Hom f g) (k x) : φ (f^[k] x) = g^[k] (φ x) :=
  φ.Semiconj.iterate_right k x

end Hom





/-! ### Core of a self-map -/

structure Core (f : α → α) (g : β → β) where
  φ : Hom f g
  ι : Hom g f
  is_inv : φ.toFun.LeftInverse ι


namespace Core

theorem ext {C C' : Core f g} (hφ : C.φ = C'.φ) (hι : C.ι = C'.ι) : C = C' := by
  cases C; cases C'; congr

theorem ext_iff {C C' : Core f g} : (C.φ = C'.φ ∧ C.ι = C'.ι) ↔ C = C' :=
  ⟨λ h ↦ ext h.1 h.2, λ h ↦ h ▸ ⟨rfl, rfl⟩⟩


def refl (f : α → α) : Core f f :=
  ⟨Hom.id f, Hom.id f, congr_fun rfl⟩

def trans (C₁ : Core f g) (C₂ : Core g h) : Core f h :=
  ⟨C₂.φ.comp C₁.φ, C₁.ι.comp C₂.ι, C₁.is_inv.comp C₂.is_inv⟩


lemma φ_comp_ι (C : Core f g) : C.φ ∘ C.ι = id :=
  funext C.is_inv

lemma φ_comp_ι_apply (C : Core f g) (x) : C.φ (C.ι x) = x :=
  C.is_inv x

lemma half_conj (C : Core f g) : C.φ ∘ f ∘ C.ι = g :=
  C.ι.semiconj ▸ congr_arg (λ s ↦ s ∘ g) C.φ_comp_ι

lemma ι_injective (C : Core f g) : C.ι.toFun.Injective :=
  C.is_inv.injective

lemma φ_surjective (C : Core f g) : C.φ.toFun.Surjective :=
  C.is_inv.surjective

end Core
