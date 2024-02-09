/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Irreducible.Component
import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Equiv
import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Sigma
import Mathlib.Logic.Equiv.Basic

/-!
# Decomposition of self-maps into irreducible components

Let `f : α → α` be a self-map.
A decomposition of `f` is a data consisting of:
* A map `P : ι → Type*`,
* A collection of self maps `F(i) : P(i) → P(i)`,
* A proof that each `F(i)` is irreducible,
* An isomorphism between `f` and the sum `Sum.map id F`.

For each irreducible component `S`, let `f_S : S → S` be its induced map.
We show that `(f_S)_S` forms a decomposition of `f`.
-/

namespace IMOSL
namespace IMO2017A3

/-- Structure expressing a decomposition of `f` -/
structure SelfMapDecomposition (f : α → α) where
  ι : Type*
  types : ι → Type*
  self_maps : (i : ι) → types i → types i
  irreducible : ∀ i : ι, irreducible (self_maps i)
  self_map_equiv : SelfMapEquiv (Sigma.map id self_maps) f





/-! ### Decomposition via irreducible components -/

namespace IrredComponent

variable (f : α → α)

def inclusion (s : Quotient (ptEquiv.mkSetoid f)) :
    SelfMapHom (IrredComponent f s) f :=
  ⟨λ a ↦ a.1, apply_fst f s⟩

def mkEquiv : SelfMapEquiv (Sigma.map _root_.id (IrredComponent f)) f where
  toEquiv := Equiv.sigmaFiberEquiv (Quotient.mk (ptEquiv.mkSetoid f))
  Semiconj := (SelfMapHom.sigma_elim (inclusion f)).Semiconj

def decomposition : SelfMapDecomposition f where
  irreducible := is_irreducible f
  self_map_equiv := mkEquiv f

/-- Existence of decompositions without explicit description -/
instance : Inhabited (SelfMapDecomposition f) := ⟨decomposition f⟩

end IrredComponent
