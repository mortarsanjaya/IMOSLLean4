/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Bundled functions betwen non-associative semirings

We define bundled functions between non-associative semirings.
We also define homomorphisms between them.
-/

namespace IMOSL
namespace IMO2012A5

structure BundledRingFun where
  protected source : Type u
  protected source_ring' : NonAssocSemiring source
  protected target : Type v
  protected target_ring' : NonAssocSemiring target
  protected f : source → target


namespace BundledRingFun

instance source_ring (X : BundledRingFun) : NonAssocSemiring X.source := X.source_ring'
instance target_ring (X : BundledRingFun) : NonAssocSemiring X.target := X.target_ring'

def ofFun [hR : NonAssocSemiring R] [hS : NonAssocSemiring S] : (R → S) → BundledRingFun :=
  BundledRingFun.mk R hR S hS





/-! ### Homomorphisms -/

structure Hom (X Y : BundledRingFun) where
  sourceHom : Y.source →+* X.source
  targetHom : X.target →+* Y.target
  spec : ∀ r, Y.f r = targetHom (X.f (sourceHom r))

namespace Hom

def id (X : BundledRingFun) : Hom X X :=
  ⟨RingHom.id X.source, RingHom.id X.target, λ _ ↦ rfl⟩

def trans (φ : Hom Y Z) (ρ : Hom X Y) : Hom X Z :=
  ⟨ρ.sourceHom.comp φ.sourceHom, φ.targetHom.comp ρ.targetHom,
    λ _ ↦ (φ.spec _).trans (φ.targetHom.congr_arg (ρ.spec _))⟩


section

variable (X : BundledRingFun) [NonAssocSemiring R]

def ofRingHom_left (φ : X.target →+* R) : Hom X (ofFun (φ ∘ X.f)) :=
  ⟨RingHom.id _, φ, λ _ ↦ rfl⟩

def ofRingHom_right (φ : R →+* X.source) : Hom X (ofFun (X.f ∘ φ)) :=
  ⟨φ, RingHom.id _, λ _ ↦ rfl⟩

end
