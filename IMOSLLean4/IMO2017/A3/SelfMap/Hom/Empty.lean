/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic
import Mathlib.Logic.Unique

/-!
# Homomorphism from the empty map

Let `ε` be an empty set and `i : ε → ε` be the empty function.
Then for any `f : α → α`, there is a unique homomorphism from `z` to `f`.
Thus, in the category of self-maps, the empty map is the initial object.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

def Hom_ofIsEmpty (hε : IsEmpty ε) (z : ε → ε) (f : α → α) : Hom z f :=
  ⟨λ x ↦ (hε.false x).elim, λ x ↦ (hε.false x).elim⟩

def EmptyHom (f : α → α) : Hom (id : Empty → Empty) f :=
  Hom_ofIsEmpty instIsEmptyEmpty _ _

instance [hε : IsEmpty ε] (z : ε → ε) (f : α → α) : Unique (Hom z f) where
  default := Hom_ofIsEmpty hε z f
  uniq := λ _ ↦ Hom.ext λ x ↦ (hε.false x).elim
