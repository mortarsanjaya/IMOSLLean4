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

/-
/-- A representative of a given quotient -/
noncomputable def quotientRep (s : Quotient (mkSetoid X)) : X.α :=
  Quotient.out (s := mkSetoid X) s

lemma quotient_eq_rep_iff {s : Quotient (mkSetoid X)} :
    s = mkQuotient X x ↔ ptEquiv X (quotientRep s) x :=
  Quotient.eq_mk_iff_out (s := mkSetoid X)

lemma rep_eq_quotient_iff {s : Quotient (mkSetoid X)} :
    mkQuotient X x = s ↔ ptEquiv X x (quotientRep s) :=
  Quotient.mk_eq_iff_out (s := mkSetoid X)

/-- A representative equivalent to a given element -/
noncomputable def eltRep (X : SelfMap) (x : X.α) :=
  quotientRep (mkQuotient X x)

lemma eltRep_equiv_self (X : SelfMap) (x : X.α) : ptEquiv X (eltRep X x) x :=
  quotient_eq_rep_iff.mp rfl

lemma eltRep_apply_eq (X : SelfMap) (x : X.α) : eltRep X (X.f x) = eltRep X x :=
  congr_arg quotientRep (mkQuotient_apply_eq X x)
-/
