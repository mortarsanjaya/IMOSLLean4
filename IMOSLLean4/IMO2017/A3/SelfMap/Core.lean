/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom

/-!
# Cores of self-maps

Given a self-map `X`, a core of `X` is a self-map `Y` with homomorphisms
  `φ : X → Y` and `ι : Y → X` such that `φ ∘ ι = id_Y`.
A core should be thought of as a "subgraph" that is a projection of `X`.
Note that unlike in the case of graphs, a core does not have to be minimal.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

structure Core (X Y : SelfMap) where
  φ : Hom X Y
  ι : Hom Y X
  is_inv : φ.toFun.LeftInverse ι



namespace Core

theorem ext {C C' : Core X Y} (hφ : C.φ = C'.φ) (hι : C.ι = C'.ι) : C = C' := by
  cases C; cases C'; congr

theorem ext_iff {C C' : Core X Y} : (C.φ = C'.φ ∧ C.ι = C'.ι) ↔ C = C' :=
  ⟨λ h ↦ ext h.1 h.2, λ h ↦ h ▸ ⟨rfl, rfl⟩⟩


def refl (X : SelfMap) : Core X X :=
  ⟨Hom.id X, Hom.id X, congr_fun rfl⟩

def trans (C₁ : Core X Y) (C₂ : Core Y Z) : Core X Z :=
  ⟨C₂.φ.comp C₁.φ, C₁.ι.comp C₂.ι, C₁.is_inv.comp C₂.is_inv⟩


lemma φ_comp_ι (C : Core X Y) : C.φ ∘ C.ι = id :=
  funext C.is_inv

lemma φ_comp_ι_apply (C : Core X Y) : ∀ a, C.φ (C.ι a) = a :=
  C.is_inv

lemma half_conj (C : Core X Y) : C.φ ∘ X.f ∘ C.ι = Y.f :=
  C.ι.semiconj ▸ congr_arg (λ s ↦ s ∘ Y.f) C.φ_comp_ι

lemma ι_injective (C : Core X Y) : C.ι.toFun.Injective :=
  C.is_inv.injective

lemma φ_surjective (C : Core X Y) : C.φ.toFun.Surjective :=
  C.is_inv.surjective



/-! ##### Binary sums -/

def sum_Core_Hom (C : Core X Y) (e : Hom Z Y) : Core (sum X Z) Y :=
  ⟨C.φ.sum_elim e, (Hom.sum_inl X Z).comp C.ι, C.is_inv⟩

def sum_Hom_Core (e : Hom X Y) (C : Core Z Y) : Core (sum X Z) Y :=
  ⟨e.sum_elim C.φ, (Hom.sum_inr X Z).comp C.ι, C.is_inv⟩

def ofHom_inl (e : Hom X Y) : Core (sum Y X) Y := sum_Core_Hom (refl Y) e

def ofHom_inr (e : Hom X Y) : Core (sum X Y) Y := sum_Hom_Core e (refl Y)



/-! ##### Sigma -/

/-- Given indexed cores `G(i)` of `F(i)`, construct `Σ G` as a core of `Σ F`. -/
def sigma_map_id (E : (i : I) → Core (F i) (G i)) :
    Core (sigma F) (sigma G) where
  φ := Hom.sigma_map_id λ i ↦ (E i).φ
  ι := Hom.sigma_map_id λ i ↦ (E i).ι
  is_inv := λ ⟨i, a⟩ ↦ Sigma.ext rfl (heq_of_eq <| (E i).is_inv a)
