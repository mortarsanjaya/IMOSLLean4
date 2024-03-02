/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Defs
import Mathlib.Logic.Function.Iterate

/-!
# Point-equivalence and irreducibility of self-maps

Let `X = ⟨α, f⟩` be a bundled self-map.
Given `a, b : α`, we denote `α ∼ b` if `f^m(a) = f^n(b)` for some `m, n : ℕ`.
One can check that `∼` defines an equivalence relation on `α`.
This equivalence is called the *point-equivalence* (with respect to `f`).
A self-map `X` is *irreducible* if `X.α` is non-empty and every
  two points in `X.α` are point-equivalent (with respect to `f`).

This is a self-map version of connectedness in graphs.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

/-- The equivalence relation -/
def ptEquiv (X : SelfMap) (a b : X.α) := ∃ m n : ℕ, X.f^[m] a = X.f^[n] b



namespace ptEquiv

lemma refl (X : SelfMap) (a : X.α) : ptEquiv X a a := ⟨0, 0, rfl⟩

lemma symm (h : ptEquiv X a b) : ptEquiv X b a :=
  h.elim λ m h ↦ h.elim λ n h ↦ ⟨n, m, h.symm⟩

lemma trans (h : ptEquiv X a b) (h0 : ptEquiv X b c) : ptEquiv X a c := by
  rcases h with ⟨m, n, h⟩
  rcases h0 with ⟨t, u, h0⟩
  refine ⟨t + m, n + u, ?_⟩
  rw [X.f.iterate_add_apply, h, X.f.iterate_add_apply, ← h0,
    ← X.f.iterate_add_apply, ← X.f.iterate_add_apply, Nat.add_comm]

theorem equivalence (X : SelfMap) : Equivalence (ptEquiv X) :=
  ⟨refl X, symm, trans⟩


section

variable (X : SelfMap) (a : X.α)

lemma of_self_iterate_left (m : ℕ) : ptEquiv X (X.f^[m] a) a :=
  ⟨0, m, rfl⟩

lemma of_self_iterate_right (m : ℕ) : ptEquiv X a (X.f^[m] a) :=
  ⟨m, 0, rfl⟩

lemma of_self_apply_left : ptEquiv X (X.f a) a :=
  of_self_iterate_left X a 1

lemma of_self_apply_right : ptEquiv X a (X.f a) :=
  of_self_iterate_right X a 1

end


section

variable (h : ptEquiv X a b)

lemma of_iterate_left (m : ℕ) : ptEquiv X (X.f^[m] a) b :=
  (of_self_iterate_left X a m).trans h

lemma of_iterate_right (m : ℕ) : ptEquiv X a (X.f^[m] b) :=
  h.trans (of_self_iterate_right X b m)

lemma of_apply_left : ptEquiv X (X.f a) b :=
  of_iterate_left h 1

lemma of_apply_right : ptEquiv X a (X.f b) :=
  of_iterate_right h 1

lemma trans_iff_left : ptEquiv X a c ↔ ptEquiv X b c :=
  ⟨trans h.symm, trans h⟩

lemma trans_iff_right : ptEquiv X c a ↔ ptEquiv X c b :=
  ⟨λ h0 ↦ h0.trans h, λ h0 ↦ h0.trans h.symm⟩

end



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



/-! ### Irreducible self-maps -/

/-- Irreducible self-maps -/
def Irreducible (X : SelfMap) := Nonempty X.α ∧ ∀ a b, ptEquiv X a b

lemma Irreducible_def (X : SelfMap) :
    Irreducible X ↔ Nonempty X.α ∧
      ∀ a b, ∃ m n : ℕ, X.f^[m] a = X.f^[n] b := by rfl
