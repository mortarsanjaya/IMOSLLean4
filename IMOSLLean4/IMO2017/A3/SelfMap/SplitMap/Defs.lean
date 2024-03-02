/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Defs

/-!
# Split maps

Let `X` be a self-map and `s : β → X.α` be a function.
The *split map* with core `X` and section `s`, denoted `SplitMap X s`, is
  the self-map on `X.α ⊕ β` defined by `X.f` on `X.α` and `X.f ∘ s` on `β`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

def SplitMap (X : SelfMap) (s : β → X.α) : SelfMap :=
  ⟨X.α ⊕ β, λ x ↦ match x with
    | Sum.inl a => Sum.inl (X.f a)
    | Sum.inr b => Sum.inl (X.f (s b))⟩


namespace SplitMap

variable (X : SelfMap) (s : β → X.α)

theorem apply_inl (a) : (SplitMap X s).f (Sum.inl a) = Sum.inl (X.f a) := rfl

theorem apply_inr (b) : (SplitMap X s).f (Sum.inr b) = Sum.inl (X.f (s b)) := rfl

theorem const_of_UnitCore (s : β → Unit) :
    ∀ x, (SplitMap UnitSelfMap s).f x = Sum.inl ()
  | Sum.inl _ => rfl
  | Sum.inr _ => rfl
