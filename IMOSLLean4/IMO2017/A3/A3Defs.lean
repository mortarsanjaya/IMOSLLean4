/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

/-!
# IMO 2017 A3

Given functions $f, g : α → α$, we say that $(f, g)$ is
  a *bad pair* if $f ∘ g ∘ f = g ∘ f ∘ g$.
We say that $f : α → α$ is said to be *good* if the only function
  $g : α → α$ such that $(f, g)$ is a bad pair is $f$.
Find all good functions.

This file provides the definitions and constructors for answers.
-/

namespace IMOSL
namespace IMO2017A3

abbrev bad_pair (f g : α → α) := f ∘ g ∘ f = g ∘ f ∘ g

/-- The problem -/
def good (f : α → α) := ∀ g : α → α, bad_pair f g → g = f

/-- The `good` map coming from `Fin 2` -/
def Fin2GoodMap (α : Type _) : Fin 2 ⊕ α → Fin 2 ⊕ α
  | Sum.inl 0 => Sum.inl 1
  | Sum.inl 1 => Sum.inl 0
  | Sum.inr _ => Sum.inl 0

/-- The `good` map coming from `Fin 3` -/
def Fin3GoodMap (α : Type _) : Fin 3 ⊕ α → Fin 3 ⊕ α
  | Sum.inl 0 => Sum.inl 1
  | Sum.inl 1 => Sum.inl 2
  | Sum.inl 2 => Sum.inl 0
  | Sum.inr _ => Sum.inl 0

/-- The `good` map coming from `Nat`, with it being `good` iff
  the requirement `GoodValuation` holds on `v` (see below). -/
def NatGoodMap (v : α → Nat) : Nat ⊕ α → Nat ⊕ α
  | Sum.inl n => Sum.inl n.succ
  | Sum.inr a => Sum.inl (v a).succ

/-- The requirement for `NatGoodMap v` to be good. -/
class GoodValuation (v : α → Nat) where
  val_non_consecutive : ∀ a a', v a ≠ (v a').succ
  val_ne_one : ∀ a, v a ≠ 1
  val_ne_two : ∀ a, v a ≠ 2
