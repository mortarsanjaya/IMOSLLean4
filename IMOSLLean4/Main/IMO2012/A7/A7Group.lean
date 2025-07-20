/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.A7.A7General
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Group.PosPart

/-!
# IMO 2012 A7, Group Version

Let `G` be a lattice ordered group.
We show that the meta-closure of a subgroup of `G` is again a subgroup of `G`.
-/

namespace IMOSL
namespace IMO2012A7

/-! ### Subgroup structure of meta-closure -/

namespace MetaClosure

variable [Lattice G] [AddGroup G] (S : AddSubgroup G)

lemma zero_mem : MetaClosure (· ∈ S) 0 := ofMem S.zero_mem

lemma pos_part_mem (ha : MetaClosure (· ∈ S) a) : MetaClosure (· ∈ S) a⁺ :=
  ofMax ha (zero_mem S)

variable [CovariantClass G G (· + ·) (· ≤ ·)]
  [CovariantClass G G (Function.swap (· + ·)) (· ≤ ·)]

lemma add_mem (ha : MetaClosure (· ∈ S) a) (hb : MetaClosure (· ∈ S) b) :
    MetaClosure (· ∈ S) (a + b) :=
  ha.recOn
    (λ ha ↦ hb.recOn
      (λ hb ↦ ofMem (S.add_mem ha hb))
      (λ _ _ ↦ by rw [add_inf]; exact ofMin)
      (λ _ _ ↦ by rw [add_sup]; exact ofMax))
    (λ _ _ ↦ by rw [inf_add]; exact ofMin)
    (λ _ _ ↦ by rw [sup_add]; exact ofMax)

lemma neg_mem (ha : MetaClosure (· ∈ S) a) : MetaClosure (· ∈ S) (-a) :=
  ha.recOn (λ ha ↦ ofMem (S.neg_mem ha))
    (λ _ _ ↦ by rw [neg_inf]; exact ofMax)
    (λ _ _ ↦ by rw [neg_sup]; exact ofMin)

lemma sub_mem (ha : MetaClosure (· ∈ S) a) (hb : MetaClosure (· ∈ S) b) :
    MetaClosure (· ∈ S) (a - b) :=
  (sub_eq_add_neg a b) ▸ add_mem S ha (neg_mem S hb)

lemma neg_part_mem (ha : MetaClosure (· ∈ S) a) : MetaClosure (· ∈ S) a⁻ :=
  ofMax (neg_mem S ha) (zero_mem S)

lemma abs_mem (ha : MetaClosure (· ∈ S) a) : MetaClosure (· ∈ S) |a| :=
  ofMax ha (neg_mem S ha)

def AddGroup_mk : AddSubgroup G :=
  { carrier := setOf (MetaClosure (· ∈ S))
    add_mem' := add_mem S
    zero_mem' := zero_mem S
    neg_mem' := neg_mem S }

theorem AddGroup_mk_carrrier {G} [DistribLattice G]
    [AddGroup G] [CovariantClass G G (· + ·) (· ≤ ·)]
    [CovariantClass G G (Function.swap (· + ·)) (· ≤ ·)](S : AddSubgroup G) :
    (AddGroup_mk S).carrier = setOf (BinOpClosure Max.max (BinOpClosure Min.min (· ∈ S))) :=
  congrArg setOf (SupInfClosure_eq_MetaClosure (· ∈ S)).symm
