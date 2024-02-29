/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

/-!
# Self-maps

This file defines self-maps as a bundled function on a type to itself.
That is, instead of defining `f : α → α` as a self-map,
  we define a self-map as the dependent pair `⟨α, f⟩`.
We also define binary sums and direct sums (while avoiding extra import).
-/

namespace IMOSL
namespace IMO2017A3

structure SelfMap where
  α : Type _
  f : α → α


namespace SelfMap

def of {α} (f : α → α) : SelfMap := ⟨α, f⟩

def EmptySelfMap : SelfMap := ⟨Empty, id⟩

def UnitSelfMap : SelfMap := ⟨Unit, id⟩

def sum (X Y : SelfMap) : SelfMap :=
  ⟨X.α ⊕ Y.α, λ a ↦ match a with
    | Sum.inl a => Sum.inl (X.f a)
    | Sum.inr a => Sum.inr (Y.f a)⟩

def sigma (X : I → SelfMap) : SelfMap :=
  ⟨(i : I) × (X i).α, λ ⟨i, a⟩ ↦ ⟨i, (X i).f a⟩⟩
