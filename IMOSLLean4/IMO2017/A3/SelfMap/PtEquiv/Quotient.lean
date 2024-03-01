/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.PtEquiv.Defs
import Mathlib.Data.Quot

/-!
# Quotient of point-equivalence

Let `X : SelfMap` be a (unbundled) self-map.
In this file, we define the quotient with respect to point-equivalence of `f`.
Then prove some properties.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace ptEquiv

/-- The setoid induced by the point equivalence -/
instance mkSetoid (X : SelfMap) : Setoid X.α := ⟨ptEquiv X, equivalence X⟩

/-- The quotient induced by the point equivalence -/
def mkQuotient (X : SelfMap) := Quotient.mk (mkSetoid X)

lemma mkQuotient_eq_iff : mkQuotient X x = mkQuotient X y ↔ ptEquiv X x y :=
  ⟨Quotient.exact, Quotient.sound (s := mkSetoid X)⟩

lemma mkQuotient_apply_eq (X : SelfMap) (x : X.α) :
    mkQuotient X (X.f x) = mkQuotient X x :=
  mkQuotient_eq_iff.mpr (of_self_apply_left X x)

lemma mkQuotient_iterate_eq (X : SelfMap) (x : X.α) :
    ∀ k, mkQuotient X (X.f^[k] x) = mkQuotient X x
  | 0 => rfl
  | k + 1 => by rw [X.f.iterate_succ_apply', mkQuotient_apply_eq,
                  mkQuotient_iterate_eq X _ k]
