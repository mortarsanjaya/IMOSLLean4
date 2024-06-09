/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Periodic

/-!
# Periodic sequence from a list

Given `l : List α` of length `N > 0`, we obtain the `N`-periodic sequence
  `a : ℕ → α` defined by `a(n) = l[n % N]` for all `n : ℕ`.
Conversely, an `N`-periodic sequence can be encoded in a list of length `N`.

We provide an implementation for both cases.
However, we want to avoid the assumption that `l` is non-empty.
Thus, we use a default value when `l` is empty and assume that `α` is inhabited.
-/

namespace IMOSL
namespace Extra

variable [Inhabited α]

def NatSeq_ofList (l : List α) (n : ℕ) : α := l.getI (n % l.length)

lemma NatSeq_ofList_periodic (l : List α) :
    Function.Periodic (NatSeq_ofList l) l.length :=
  λ n ↦ congrArg l.getI (n.add_mod_right l.length)

lemma NatSeq_of_singleton (c : α) (n : ℕ) : NatSeq_ofList [c] n = c := by
  rw [NatSeq_ofList, List.length_singleton, Nat.mod_one]; rfl

lemma NatSeq_of_nil (n : ℕ) : NatSeq_ofList [] n = default (α := α) := rfl

lemma NatSeq_nonempty_eq_get {l : List α} (h : l ≠ []) (n : ℕ) :
    NatSeq_ofList l n = l.get ⟨n % l.length, n.mod_lt (List.length_pos.mpr h)⟩ :=
  l.getI_eq_get _

def List_ofNatSeq (a : ℕ → α) (N : ℕ) : List α := (List.range N).map a

lemma List_ofNatSeq_length (a : ℕ → α) (N : ℕ) : (List_ofNatSeq a N).length = N :=
  (List.length_map _ _).trans (List.length_range N)

lemma List_ofNatSeq_nonempty (a : ℕ → α) (hN : 0 < N) : List_ofNatSeq a N ≠ [] :=
  List.length_pos.mp (hN.trans_eq (List_ofNatSeq_length a N).symm)

lemma NatSeq_ofList_of_PeriodicNatSeq_eq (hN : 0 < N) {a : ℕ → α} (ha : a.Periodic N) :
    NatSeq_ofList (List_ofNatSeq a N) = a :=
  funext λ n ↦ by
    replace hN := List.length_pos.mp <| hN.trans_eq (List_ofNatSeq_length a N).symm
    rw [NatSeq_nonempty_eq_get hN]; unfold List_ofNatSeq
    rw [List.get_map, List.get_range, Fin.val_mk,
      List.length_map, List.length_range, ha.map_mod_nat]
