/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.SplitMap.Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Core.Defs

/-!
# Core of a split map is a core

Let `X` be a self-map and `s : β → X.α` be a function.
We construct the canonical core instance of `X` over `SplitMap X s`.
In fact, this core is dense; we will not prove it here.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace SplitMap

variable (X : SelfMap) (s : β → X.α)

def toCoreHom : Hom (SplitMap X s) X :=
  ⟨Sum.elim id s, Sum.rec (λ _ ↦ rfl) (λ _ ↦ rfl)⟩

def fromCoreHom : Hom X (SplitMap X s) :=
  ⟨Sum.inl, λ _ ↦ rfl⟩

def toCore : Core (SplitMap X s) X :=
  ⟨toCoreHom X s, fromCoreHom X s, λ _ ↦ rfl⟩
