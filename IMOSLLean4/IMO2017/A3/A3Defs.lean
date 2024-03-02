/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Defs

/-!
# IMO 2017 A3 (Definitions)

Given self-maps $f, g : α → α$, we say that $(f, g)$ is
  a *bad pair* if $f ∘ g ∘ f = g ∘ f ∘ g$.
We say that $f : α → α$ is said to be *good* if the only function
  $g : α → α$ such that $(f, g)$ is a bad pair is $f$.
Find all good self-maps.

This file provides the definitions and constructors for answers.
We will use the bundled version of self-maps from `SelfMap/Defs`.
-/

namespace IMOSL
namespace IMO2017A3

abbrev bad_pair (f g : α → α) := f ∘ g ∘ f = g ∘ f ∘ g

/-- The problem -/
def good (X : SelfMap) := ∀ g : X.α → X.α, bad_pair X.f g → g = X.f

/-- The `good` map coming from `Fin 2` -/
def Fin2GoodMap (α : Type _) : SelfMap :=
  ⟨Fin 2 ⊕ α, λ x ↦ match x with
    | Sum.inl 0 => Sum.inl 1
    | Sum.inl 1 => Sum.inl 0
    | Sum.inr _ => Sum.inl 0⟩

/-- The `good` map coming from `Fin 3` -/
def Fin3GoodMap (α : Type _) : SelfMap :=
  ⟨Fin 3 ⊕ α, λ x ↦ match x with
    | Sum.inl 0 => Sum.inl 1
    | Sum.inl 1 => Sum.inl 2
    | Sum.inl 2 => Sum.inl 0
    | Sum.inr _ => Sum.inl 0⟩

/-- The `good` map coming from `Nat`, with it being `good` iff
  the requirement `GoodValuation` holds on `v` (see below). -/
def NatGoodMap (v : α → Nat) : SelfMap :=
  ⟨Nat ⊕ α, λ x ↦ match x with
    | Sum.inl n => Sum.inl n.succ
    | Sum.inr a => Sum.inl (v a).succ⟩

/-- The requirement for `NatGoodMap v` to be good. -/
class GoodValuation (v : α → Nat) where
  val_non_consecutive : ∀ a a', v a ≠ (v a').succ
  val_ne_one : ∀ a, v a ≠ 1
  val_ne_two : ∀ a, v a ≠ 2
