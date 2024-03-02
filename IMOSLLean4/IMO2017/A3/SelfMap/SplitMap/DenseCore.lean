/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.SplitMap.Core
import IMOSLLean4.IMO2017.A3.SelfMap.Core.Dense

/-!
# Core of a split map is a dense core

We prove that as the canonical core, `X` is dense over `SplitMap X s`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace SplitMap

def toDenseCore : DenseCore (SplitMap X s) X :=
  ⟨toCore X s, λ x ↦ match x with
    | Sum.inl a => ⟨a, ptEquiv.refl _ _⟩
    | Sum.inr b => ⟨s b, 1, 1, rfl⟩⟩
