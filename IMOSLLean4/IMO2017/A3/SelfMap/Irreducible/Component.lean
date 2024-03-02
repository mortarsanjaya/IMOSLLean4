/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Irreducible.Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Subtype

/-!
# Irreducible self-maps and irreducible component of self-maps

Let `X` be a self-map and `∼` be the point-equivalence relation.
For each equivalence class `S`, there is an induced restriction map `S → S`.
We call this (bundled) map an *irreducible component* of `X`.
We show that this restriction map is irreducible.
Furthermore, we show that these maps give a decomposition of `X`.

This is a self-map version of connected components of a graph.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

namespace ptEquiv

/-! ### Quotient with respect to point-equivalence -/

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

end ptEquiv



/-! ### Irreducible components -/

namespace Irreducible

variable (X : SelfMap) (s : Quotient (ptEquiv.mkSetoid X))

def Component : SelfMap where
  α := {a // Quotient.mk (ptEquiv.mkSetoid X) a = s}
  f := λ ⟨a, h⟩ ↦ ⟨X.f a, h ▸ ptEquiv.mkQuotient_apply_eq X _⟩

lemma Component_nonempty : Nonempty (Component X s).α :=
  s.exists_rep.elim λ a h ↦ ⟨a, h⟩

lemma apply_fst (b : (Component X s).α) :
    ((Component X s).f b).1 = X.f b.1 := rfl

lemma iterate_apply_fst : ∀ (k : ℕ) (b),
    ((Component X s).f^[k] b).1 = X.f^[k] b.1
  | 0, _ => rfl
  | m + 1, _ => by rw [Function.iterate_succ_apply', apply_fst,
                  iterate_apply_fst m, X.f.iterate_succ_apply']

lemma is_irreducible : Irreducible (Component X s) :=
  ⟨Component_nonempty X s, λ a b ↦ by
    rcases Quotient.exact (a.2.trans b.2.symm) with ⟨m, n, h⟩
    refine ⟨m, n, Subtype.ext ?_⟩
    rwa [iterate_apply_fst, iterate_apply_fst]⟩



/-! ### Decomposition via irreducible components -/

def Component_inclusion : Hom (Component X s) X :=
  ⟨λ a ↦ a.1, apply_fst X s⟩

def mkEquivComponentSigma : Equiv (sigma (Component X)) X where
  toEquiv := Equiv.sigmaFiberEquiv (Quotient.mk (ptEquiv.mkSetoid X))
  Semiconj := (SelfMap.Hom.sigma_elim (Component_inclusion X)).Semiconj
