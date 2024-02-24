/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic
import Mathlib.Data.Sigma.Basic

/-!
# Sums of homomorphisms between self-maps

Let `F(i) : α(i) → α(i)` and `G(i) : β(i) → β(i)` denote indexed self-maps
  with the same indexing, and let `g : β → β` be a self-map.
We construct some homomorphisms on sigma types.
* We construct the induced inclusion `F(i) → Σ F(i)`.
* Given self-map homomorphisms `F(i) → g`, we construct
  the induced self-map homomorphism `Σ F(i) → g`.
* Given indexed homomorphisms `F(i) → G(i)`, we construct
  the induced self-map homomorphism `Σ F(i) → Σ G(i)`.
* If each `G(i)` is a core of `F(i)`, we construct
  a core instance of `Σ G(i)` over `Σ F(i)`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

variable {α β : I → Type*} {F : (i : I) → α i → α i} {G : (i : I) → β i → β i}

namespace Hom

section

variable (F : (i : I) → α i → α i)

def sigma_incl (i : I) : Hom (F i) (Sigma.map _root_.id F) :=
  ⟨λ a ↦ ⟨i, a⟩, λ _ ↦ rfl⟩

lemma sigma_incl_apply (a : α i) : sigma_incl F i a = ⟨i, a⟩ := rfl

end



section

variable (e : (i : I) → Hom (F i) g)

/-- Given a collection of self-map homomorphisms `F(i) → g`,
  construct the self-map homomorphism `Σ F(i) → g`. -/
def sigma_elim : Hom (Sigma.map _root_.id F) g :=
  ⟨λ p ↦ e p.1 p.2, λ p ↦ (e p.1).Semiconj p.2⟩

lemma sigma_elim_apply (p : Sigma α) : sigma_elim e p = e p.1 p.2 := rfl

lemma sigma_elim_apply' (a : α i) : sigma_elim e ⟨i, a⟩ = e i a := rfl

end



section

variable (E : (i : I) → Hom (F i) (G i))

/-- Given a collection of self-map homomorphisms `F(i) → G(i)`,
  construct the self-map homomorphism `Σ F(i) → Σ G(i)`. -/
def sigma_map : Hom (Sigma.map _root_.id F) (Sigma.map _root_.id G) :=
  ⟨λ p ↦ ⟨p.1, E p.1 p.2⟩,
  λ p ↦ Sigma.ext rfl (heq_of_eq <| (E p.1).Semiconj p.2)⟩

lemma sigma_map_apply (p : Sigma α) : sigma_map E p = ⟨p.1, E p.1 p.2⟩ := rfl

lemma sigma_map_apply' (a : α i) : sigma_map E ⟨i, a⟩ = ⟨i, E i a⟩ := rfl

end

end Hom



namespace Core

/-- Given a collection of self-map homomorphisms `F(i) → G(i)`,
  construct the self-map homomorphism `Σ F(i) → Σ G(i)`. -/
def sigma_map (E : (i : I) → Core (F i) (G i)) :
    Core (Sigma.map id F) (Sigma.map id G) where
  φ := Hom.sigma_map λ i ↦ (E i).φ
  ι := Hom.sigma_map λ i ↦ (E i).ι
  is_inv := λ p ↦ Sigma.ext rfl (heq_of_eq <| (E p.1).is_inv p.2)

/-- Given `f` as a core of `G(i)` across all `i`, and a fixed `i`,
  construct a core instance of `f` over `Σ G(i)`. -/
def sigma_fixed_src (e : (i : I) → Core (G i) f) (i : I) :
    Core (Sigma.map id G) f where
  φ := Hom.sigma_elim λ i ↦ (e i).φ
  ι := (Hom.sigma_incl G i).comp (e i).ι
  is_inv := (e i).is_inv

end Core
