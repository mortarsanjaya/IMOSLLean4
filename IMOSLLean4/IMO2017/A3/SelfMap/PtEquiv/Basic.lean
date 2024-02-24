/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Logic.Function.Iterate

/-!
# Point-equivalence of self-maps

Let `f : α → α` be a self-map.
Given `a, b : α`, we denote `α ∼ b` if `f^m(a) = f^n(b)` for some `m, n : ℕ`.
One can check that `∼` defines an equivalence relation on `α`.
This equivalence is called the *point-equivalence* (with respect to `f`).
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

variable {α : Type*}

/-- The equivalence relation -/
def ptEquiv (f : α → α) (a b : α) := ∃ m n : ℕ, f^[m] a = f^[n] b



namespace ptEquiv

lemma refl (f : α → α) (a : α) : ptEquiv f a a := ⟨0, 0, rfl⟩

lemma symm (h : ptEquiv f a b) : ptEquiv f b a :=
  h.elim λ m h ↦ h.elim λ n h ↦ ⟨n, m, h.symm⟩

lemma trans (h : ptEquiv f a b) (h0 : ptEquiv f b c) : ptEquiv f a c := by
  rcases h with ⟨m, n, h⟩
  rcases h0 with ⟨t, u, h0⟩
  refine ⟨t + m, n + u, ?_⟩
  rw [f.iterate_add_apply, h, f.iterate_add_apply, ← h0,
    ← f.iterate_add_apply, ← f.iterate_add_apply, Nat.add_comm]

theorem equivalence (f : α → α) : Equivalence (ptEquiv f) :=
  ⟨refl f, symm, trans⟩


section

variable (f : α → α) (a : α)

lemma of_self_iterate_left (m : ℕ) : ptEquiv f (f^[m] a) a :=
  ⟨0, m, rfl⟩

lemma of_self_iterate_right (m : ℕ) : ptEquiv f a (f^[m] a) :=
  ⟨m, 0, rfl⟩

lemma of_self_apply_left : ptEquiv f (f a) a :=
  of_self_iterate_left f a 1

lemma of_self_apply_right : ptEquiv f a (f a) :=
  of_self_iterate_right f a 1

end


section

variable (h : ptEquiv f a b)

lemma of_iterate_left (m : ℕ) : ptEquiv f (f^[m] a) b :=
  (of_self_iterate_left f a m).trans h

lemma of_iterate_right (m : ℕ) : ptEquiv f a (f^[m] b) :=
  h.trans (of_self_iterate_right f b m)

lemma of_apply_left : ptEquiv f (f a) b :=
  of_iterate_left h 1

lemma of_apply_right : ptEquiv f a (f b) :=
  of_iterate_right h 1

end
