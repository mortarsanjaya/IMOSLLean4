/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.PtEquiv.Basic
import Mathlib.Data.Quot

/-!
# Quotient of point-equivalence

Let `f : α → α` be a self-map and `∼` denote the point-equivalence.
In this file, we define the quotient with respect to `∼`
  and prove some properties.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace ptEquiv

variable {α : Type*}

/-- The setoid induced by the point equivalence -/
instance mkSetoid (f : α → α) : Setoid α := ⟨ptEquiv f, equivalence f⟩

/-- The quotient induced by the point equivalence -/
def mkQuotient (f : α → α) := Quotient.mk (mkSetoid f)

lemma mkQuotient_eq_iff {f : α → α} {x y : α} :
    mkQuotient f x = mkQuotient f y ↔ ptEquiv f x y :=
  Quotient.eq (r := mkSetoid f)

lemma mkQuotient_apply_eq (f : α → α) (x : α) :
    mkQuotient f (f x) = mkQuotient f x :=
  mkQuotient_eq_iff.mpr (of_self_apply_left f x)

lemma mkQuotient_iterate_eq (f : α → α) (x : α) :
    ∀ k, mkQuotient f (f^[k] x) = mkQuotient f x
  | 0 => rfl
  | k + 1 => by rw [f.iterate_succ_apply', mkQuotient_apply_eq,
                  mkQuotient_iterate_eq f _ k]

/-- A representative of a given quotient -/
noncomputable def quotientRep {f : α → α} (s : Quotient (mkSetoid f)) : α :=
  Quotient.out (s := mkSetoid f) s

lemma quotient_eq_rep_iff {s : Quotient (mkSetoid f)} {x : α} :
    s = mkQuotient f x ↔ ptEquiv f (quotientRep s) x :=
  Quotient.eq_mk_iff_out (s := mkSetoid f)

lemma rep_eq_quotient_iff {x : α} {s : Quotient (mkSetoid f)} :
    mkQuotient f x = s ↔ ptEquiv f x (quotientRep s) :=
  Quotient.mk_eq_iff_out (s := mkSetoid f)

/-- A representative equivalent to a given element -/
noncomputable def eltRep (f : α → α) (x : α) := quotientRep (mkQuotient f x)

lemma eltRep_equiv_self (f : α → α) (x : α) : ptEquiv f (eltRep f x) x :=
  quotient_eq_rep_iff.mp rfl

lemma eltRep_apply_eq (f : α → α) (x : α) : eltRep f (f x) = eltRep f x :=
  congr_arg quotientRep (mkQuotient_apply_eq f x)
