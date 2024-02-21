/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic
import Mathlib.Data.Sigma.Basic

/-!
# Sums of homomorphisms between self-maps

Fix an indexed self-map `F(i) : α(i) → α(i)`.
Given a self-map `g : β → β` and self-map homomorphisms `F(i) → g`,
  there is an induced self-map homomorphism `Σ F(i) → g`.
This file constructs this map.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace Hom

variable {α : ι → Type*} {F : (i : ι) → α i → α i} (e : (i : ι) → Hom (F i) g)

/-- Given a collection of self-map homomorphisms `F(i) → g`,
  construct the self-map homomorphism `Σ F(i) → g`. -/
def sigma_mk : Hom (Sigma.map _root_.id F) g :=
  ⟨λ p ↦ e p.1 p.2, λ p ↦ (e p.1).Semiconj p.2⟩

lemma sigma_mk_apply (p : (i : ι) × α i) : (sigma_mk e) p = e p.1 p.2 := rfl

lemma sigma_mk_apply' (a : α i) : (sigma_mk e) ⟨i, a⟩ = e i a := rfl
