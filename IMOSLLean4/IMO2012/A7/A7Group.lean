/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A7.A7General
import Mathlib.GroupTheory.Subgroup.Basic
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

variable [Lattice G] [AddGroup G] [CovariantClass G G (· + ·) (· ≤ ·)]
    [CovariantClass G G (Function.swap (· + ·)) (· ≤ ·)]

variable (S : AddSubgroup G)

lemma add_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) (hb : MetaClosure (λ x ↦ x ∈ S) b) :
    MetaClosure (λ x ↦ x ∈ S) (a + b) :=
  ha.recOn
    (λ ha ↦ hb.recOn
      (λ hb ↦ ofMem (S.add_mem ha hb))
      (λ _ _ ↦ by rw [add_inf]; exact ofInf)
      (λ _ _ ↦ by rw [add_sup]; exact ofSup))
    (λ _ _ ↦ by rw [inf_add]; exact ofInf)
    (λ _ _ ↦ by rw [sup_add]; exact ofSup)

lemma zero_mem : MetaClosure (λ x ↦ x ∈ S) 0 := ofMem S.zero_mem

lemma neg_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) : MetaClosure (λ x ↦ x ∈ S) (-a) :=
  ha.recOn (λ ha ↦ ofMem (S.neg_mem ha))
    (λ _ _ ↦ by rw [neg_inf]; exact ofSup)
    (λ _ _ ↦ by rw [neg_sup]; exact ofInf)

lemma sub_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) (hb : MetaClosure (λ x ↦ x ∈ S) b) :
    MetaClosure (λ x ↦ x ∈ S) (a - b) :=
  (sub_eq_add_neg a b) ▸ add_mem S ha (neg_mem S hb)

lemma pos_part_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) : MetaClosure (λ x ↦ x ∈ S) a⁺ :=
  ofSup ha (zero_mem S)

lemma neg_part_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) : MetaClosure (λ x ↦ x ∈ S) a⁻ :=
  ofSup (neg_mem S ha) (zero_mem S)

lemma abs_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) : MetaClosure (λ x ↦ x ∈ S) |a| :=
  ofSup ha (neg_mem S ha)

def AddGroup_mk : AddSubgroup G :=
  { carrier := {a | MetaClosure (λ x ↦ x ∈ S) a}
    add_mem' := add_mem S
    zero_mem' := zero_mem S
    neg_mem' := neg_mem S }

end MetaClosure





/-! ### Subgroup structure via `BinOpClosure` -/

theorem SupInfClosure_exists_Subgroup [DistribLattice G]
    [AddGroup G] [CovariantClass G G (· + ·) (· ≤ ·)]
    [CovariantClass G G (Function.swap (· + ·)) (· ≤ ·)] (S : AddSubgroup G) :
    ∃ T : AddSubgroup G, T.carrier =
      setOf (BinOpClosure Sup.sup (BinOpClosure Inf.inf (λ x ↦ x ∈ S))) :=
  SupInfClosure_eq_MetaClosure (λ x ↦ x ∈ S) ▸ ⟨MetaClosure.AddGroup_mk S, rfl⟩
