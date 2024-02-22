/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Equiv
import IMOSLLean4.IMO2017.A3.SelfMap.Irreducible.Basic
import Mathlib.Data.Sigma.Basic

/-!
# Decomposition of self-maps into irreducible components

Let `f : α → α` be a self-map.
A decomposition of `f` is a data consisting of:
* A map `P : ι → Type*`,
* A collection of self maps `F(i) : P(i) → P(i)`,
* A proof that each `F(i)` is irreducible,
* An isomorphism between `f` and the sum `Sum.map id F`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

/-- Structure expressing a decomposition of `f` -/
structure Decomposition (f : α → α) where
  ι : Type*
  types : ι → Type*
  SelfMaps : (i : ι) → types i → types i
  type_nonempty : ∀ i : ι, Nonempty (types i)
  irreducible : ∀ i : ι, irreducible (SelfMaps i)
  SelfMap_equiv : Equiv (Sigma.map id SelfMaps) f
