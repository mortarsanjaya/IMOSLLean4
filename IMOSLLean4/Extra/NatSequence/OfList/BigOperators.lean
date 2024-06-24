/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.NatSequence.OfList.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# Big operators over periodic sequences coming from list

We prove some results regarding sums and products over periodic sequences.
-/

namespace IMOSL
namespace Extra

open Finset

variable [CommMonoid M]

@[to_additive] local instance MonoidInhabited : Inhabited M := ⟨1⟩

@[to_additive] theorem periodic_prod_add_right {a : ℕ → M} (h : a.Periodic n) (k) :
    (range n).prod (λ i ↦ a (i + k)) = (range n).prod a :=
  match k, n with
  | 0, n => rfl
  | k + 1, 0 => rfl
  | k + 1, n + 1 => by
      rw [← periodic_prod_add_right h k, prod_range_succ,
        prod_range_succ', Nat.zero_add, Nat.add_left_comm, h]
      refine congrArg₂ _ (congrArg₂ Finset.prod rfl (funext λ i ↦ ?_)) rfl
      rw [Nat.succ_add, Nat.add_succ]



namespace NatSeqOfList

@[to_additive] theorem range_prod_eq :
    ∀ l : List M, (range l.length).prod (NatSeqOfList l) = l.prod
  | [] => rfl
  | a :: l => by
      rw [l.length_cons, prod_range_succ', List.prod_cons,
        cons_zero, mul_comm, ← range_prod_eq]
      refine congrArg _ (prod_congr rfl λ k hk ↦ ?_)
      rw [mem_range] at hk
      unfold NatSeqOfList
      rw [Nat.mod_eq_of_lt hk, l.length_cons, Nat.mod_eq_of_lt (Nat.succ_lt_succ hk)]; rfl

@[to_additive] theorem range_prod_add_right (l : List M) (k : ℕ) :
    (range l.length).prod (λ i ↦ NatSeqOfList l (i + k)) = l.prod := by
  rw [periodic_prod_add_right (periodic l), range_prod_eq]

@[to_additive] theorem range_prod_eq_Cyclic2Map_prod (f : M → M → M) (l : List M) :
    (range l.length).prod (λ i ↦ f (NatSeqOfList l i) (NatSeqOfList l i.succ))
      = (cyclic2Map f l).prod := by
  rw [← range_prod_eq, cyclic2Map_length]
  refine prod_congr rfl λ k h ↦ (cyclic2Map_NatSeq_of_nonempty f ?_ k).symm
  exact List.length_pos.mp (Nat.zero_lt_of_lt (mem_range.mp h))
