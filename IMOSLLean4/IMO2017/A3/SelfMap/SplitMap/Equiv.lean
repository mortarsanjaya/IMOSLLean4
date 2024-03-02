/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.SplitMap.Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Equiv.Defs
import Mathlib.Logic.Equiv.Basic

/-!
# Isomorphism between split maps

We provide some self-map isomorphisms involving split maps.
-/

namespace IMOSL
namespace IMO2017A3

def sumSumSumCommFn (α β γ δ : Type*) :
    (α ⊕ β) ⊕ (γ ⊕ δ) → (α ⊕ γ) ⊕ (β ⊕ δ)
  | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
  | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
  | Sum.inr (Sum.inl c) => Sum.inl (Sum.inr c)
  | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)

lemma sumSumSumComm_inv (α β γ δ : Type*) :
    ∀ x, sumSumSumCommFn α γ β δ (sumSumSumCommFn α β γ δ x) = x
  | Sum.inl (Sum.inl _) => rfl
  | Sum.inl (Sum.inr _) => rfl
  | Sum.inr (Sum.inl _) => rfl
  | Sum.inr (Sum.inr _) => rfl

def sumSumSumCommEquiv (α β γ δ : Type*) :
    (α ⊕ β) ⊕ (γ ⊕ δ) ≃ (α ⊕ γ) ⊕ (β ⊕ δ) where
  toFun := sumSumSumCommFn α β γ δ
  invFun := sumSumSumCommFn α γ β δ
  left_inv := sumSumSumComm_inv α β γ δ
  right_inv := sumSumSumComm_inv α γ β δ



namespace SelfMap
namespace SplitMap

def sumEquiv (X₁ X₂ : SelfMap) (s₁ : β₁ → X₁.α) (s₂ : β₂ → X₂.α) :
    Equiv (sum (SplitMap X₁ s₁) (SplitMap X₂ s₂))
      (SplitMap (sum X₁ X₂) (Sum.map s₁ s₂)) where
  toEquiv := sumSumSumCommEquiv _ _ _ _
  Semiconj := λ x ↦ match x with
    | Sum.inl (Sum.inl _) => rfl
    | Sum.inl (Sum.inr _) => rfl
    | Sum.inr (Sum.inl _) => rfl
    | Sum.inr (Sum.inr _) => rfl

def sigmaEquiv (X) {β : I → Type*} (s : (i : I) → β i → (X i).α) :
    Equiv (sigma λ i ↦ SplitMap (X i) (s i))
      (SplitMap (sigma X) (Sigma.map id s)) where
  toEquiv := Equiv.sigmaSumDistrib _ _
  Semiconj := λ ⟨_, x⟩ ↦ match x with
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl

def emptyEquiv (s : β → Empty) :
    Equiv EmptySelfMap (SplitMap EmptySelfMap s) where
  toFun := Empty.elim
  invFun := λ x ↦ match x with
    | Sum.inl a => a.elim
    | Sum.inr b => (s b).elim
  left_inv := λ x ↦ x.elim
  right_inv := λ x ↦ match x with
    | Sum.inl a => a.elim
    | Sum.inr b => (s b).elim
  Semiconj := λ x ↦ x.elim
