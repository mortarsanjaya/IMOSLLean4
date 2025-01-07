/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.ExcellentFun.AddMonoidHom
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Excellent functions and ring homomorphisms

Let `φ : R →+* S` be a ring homomorphism and `G` be an abelian group.
Then for any `f : S → G` excellent, `φ ∘ f` is also excellent.
If `φ` is surjective, then this composition is injective, and
  `IsOfAddMonoidHomSurjective S G` implies `IsOfAddMonoidHomSurjective R G`.
-/

namespace IMOSL
namespace IMO2017A6
namespace ExcellentFun

variable [NonAssocRing R] [NonAssocRing S] (φ : R →+* S)
include φ

/-- Composition of an excellent function with a ring homomorphism. -/
def RingHomComp [Add G] (f : ExcellentFun S G) : ExcellentFun R G where
  toFun x := f (φ x)
  excellent_def' x y := by simpa using f.excellent_def' (φ x) (φ y)

/-- `RingHomComp` as a group homomorphism. -/
def RingHomCompHom [AddCommMonoid G] : ExcellentFun S G →+ ExcellentFun R G where
  toFun := RingHomComp φ
  map_zero' := rfl
  map_add' _ _ := rfl


variable (hφ : Function.Surjective φ)
include hφ

theorem RingHomComp_injective [Add G] : (RingHomComp φ (G := G)).Injective := by
  refine λ _ _ h ↦ ExcellentFun.ext λ x ↦ ?_
  obtain ⟨y, rfl⟩ := hφ x; exact ExcellentFun.ext_iff.mp h y

theorem RingHomCompHom_injective [AddCommMonoid G] :
    Function.Injective (RingHomCompHom φ (G := G)) :=
  RingHomComp_injective φ hφ

theorem IsOfAddMonoidHomSurjective.ofSurjectiveRingHom
    [AddZeroClass G] [IsOfAddMonoidHomSurjective R G] :
    IsOfAddMonoidHomSurjective S G := by
  refine ⟨λ f ↦ ?_⟩
  obtain ⟨ρ, h⟩ := ofAddMonoidHom_surjective (f.RingHomComp φ)
  replace h (x : R) : ρ x = f (φ x) := ExcellentFun.ext_iff.mp h x
  refine ⟨⟨⟨f, by simpa only [map_zero] using (h 0).symm⟩, λ x y ↦ ?_⟩, rfl⟩
  obtain ⟨a, rfl⟩ := hφ x; obtain ⟨b, rfl⟩ := hφ y
  simpa only [h, φ.map_add] using ρ.map_add a b
