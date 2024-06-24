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

In the implementation, we want to avoid the assumption that `l` is non-empty.
Thus, we use a default value when `l` is empty and assume that `α` is inhabited.
-/

namespace IMOSL
namespace Extra

variable [Inhabited α]

def NatSeqOfList (l : List α) (n : ℕ) : α := l.getI (n % l.length)


namespace NatSeqOfList

lemma periodic (l : List α) : (NatSeqOfList l).Periodic l.length :=
  λ n ↦ congrArg l.getI (n.add_mod_right l.length)

lemma singleton (c : α) (n : ℕ) : NatSeqOfList [c] n = c := by
  rw [NatSeqOfList, List.length_singleton, Nat.mod_one]; rfl

lemma nil (n : ℕ) : NatSeqOfList [] n = default (α := α) := rfl

lemma cons_zero (a : α) (l) : NatSeqOfList (a :: l) 0 = a := rfl

lemma nonempty_eq_get {l : List α} (h : l ≠ []) (n : ℕ) :
    NatSeqOfList l n = l.get ⟨n % l.length, n.mod_lt (List.length_pos.mpr h)⟩ :=
  l.getI_eq_get _

lemma rotate_apply (l : List α) (n k : ℕ) :
    NatSeqOfList (l.rotate n) k = NatSeqOfList l (k + n) :=
  match l, n with
  | [], _ => rfl
  | l, 0 => by rw [l.rotate_zero, k.add_zero]
  | a :: l, n + 1 => by
      rw [List.rotate_cons_succ, rotate_apply, ← k.add_assoc, NatSeqOfList, NatSeqOfList,
        List.length_append, List.length_singleton, List.length_cons, ← (k + n).mod_add_mod]
      generalize hx : (k + n) % l.length.succ = x
      replace hx : x < l.length ∨ x = l.length := by
        rw [← Nat.lt_succ_iff_lt_or_eq, ← hx]
        exact Nat.mod_lt _ (Nat.succ_pos _)
      rcases hx with hx | rfl
      · rw [Nat.mod_eq_of_lt (Nat.succ_lt_succ hx), List.getI_append _ _ _ hx]; rfl
      · rw [List.getI_append_right _ _ _ (Nat.le_refl _), Nat.mod_self, Nat.sub_self]; rfl

lemma of_range_map (hN : 0 < N) {a : ℕ → α} (ha : a.Periodic N) :
    NatSeqOfList ((List.range N).map a) = a :=
  funext λ n ↦ by
    replace hN : (List.range N).map a ≠ [] := by
      rwa [← List.length_pos, List.length_map, List.length_range]
    rw [NatSeqOfList.nonempty_eq_get hN, List.get_map, List.get_range,
      Fin.val_mk, List.length_map, List.length_range, ha.map_mod_nat]


section

variable (f : α → α → α) (l : List α)

/-- From `[a_0, …, a_{n - 1}]`, get `[f(a_0, a_1), …, f(a_{n - 1}, a_0)]`. -/
def cyclic2Map : List α :=
  (List.range l.length).map λ n ↦ f (NatSeqOfList l n) (NatSeqOfList l n.succ)

lemma cyclic2Map_length : (cyclic2Map f l).length = l.length := by
  rw [cyclic2Map, List.length_map, List.length_range]

lemma cyclic2Map_nil : cyclic2Map f [] = [] := rfl

lemma cyclic2Map_NatSeq_of_nonempty {l : List α} (h : l ≠ []) :
    ∀ n, NatSeqOfList (cyclic2Map f l) n = f (NatSeqOfList l n) (NatSeqOfList l n.succ) :=
  have h0 := periodic l
  congrFun <| of_range_map (List.length_pos.mpr h) λ n ↦ by rw [h0, ← Nat.succ_add, h0]

lemma cyclic2Map_NatSeq_of_fun {f : α → α → α} (h : f default default = default) (l n) :
    NatSeqOfList (cyclic2Map f l) n = f (NatSeqOfList l n) (NatSeqOfList l n.succ) :=
  match l with
  | [] => h.symm
  | a :: l => cyclic2Map_NatSeq_of_nonempty f (List.cons_ne_nil a l) n
