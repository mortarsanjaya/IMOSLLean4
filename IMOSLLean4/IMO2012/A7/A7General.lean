/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Order.Lattice

/-!
# IMO 2012 A7, General Version

Given a lattice `α`, the *inf-closure* (resp. *sup-closure*) of a subset `S ⊆ α` is the
  smallest set containing `S` that is closed under infimum (resp. supremum).
The *meta-closure* of `S` is the sup-closure of the inf-closure of `S`.

Suppose that `α` is a distributive lattice.
We show that the meta-closure of `S` is exactly the smallest set
  containing `S` that is closed under infimum and supremum simultaneously.
-/

namespace IMOSL
namespace IMO2012A7

/-- The "alternative" lattice closure under infimum and supremum -/
inductive MetaClosure [Lattice α] (P : α → Prop) : α → Prop where
  | ofMem (_ : P a) : MetaClosure P a
  | ofMin (_ : MetaClosure P a) (_ : MetaClosure P b) : MetaClosure P (a ⊓ b)
  | ofMax (_ : MetaClosure P a) (_ : MetaClosure P b) : MetaClosure P (a ⊔ b)

inductive BinOpClosure (op : α → α → α) (P : α → Prop) : α → Prop where
  | ofMem (_ : P a) : BinOpClosure op P a
  | ofOp (_ : BinOpClosure op P a) (_ : BinOpClosure op P b) : BinOpClosure op P (op a b)



section Lattice

variable [Lattice α] (P : α → Prop)

lemma InfClosure_imp_MetaClosure (h : BinOpClosure Min.min P a) : MetaClosure P a :=
  h.recOn MetaClosure.ofMem λ _ _ ↦ MetaClosure.ofMin

lemma SupInfClosure_imp_MetaClosure
    (h : BinOpClosure Max.max (BinOpClosure Min.min P) a) : MetaClosure P a :=
  h.recOn (InfClosure_imp_MetaClosure P) (λ _ _ ↦ MetaClosure.ofMax)

end Lattice



section Distrib

variable [DistribLattice α] (P : α → Prop)

lemma MetaClosure_imp_SupInfClosure (h : MetaClosure P a) :
    BinOpClosure Max.max (BinOpClosure Min.min P) a :=
  h.recOn (λ h ↦ BinOpClosure.ofMem (BinOpClosure.ofMem h))
    (λ _ _ ha hb ↦ ha.recOn
      (λ ha ↦ hb.recOn
        (λ hb ↦ BinOpClosure.ofMem (BinOpClosure.ofOp ha hb))
        (λ _ _ ↦ inf_sup_left (α := α) _ _ _ ▸ BinOpClosure.ofOp))
      (λ _ _ ↦ inf_sup_right (α := α) _ _ _ ▸ BinOpClosure.ofOp))
    (λ _ _ ↦ BinOpClosure.ofOp)

lemma SupInfClosure_iff_MetaClosure :
    BinOpClosure Max.max (BinOpClosure Min.min P) a ↔ MetaClosure P a :=
  ⟨SupInfClosure_imp_MetaClosure P, MetaClosure_imp_SupInfClosure P⟩

lemma SupInfClosure_eq_MetaClosure :
    BinOpClosure Max.max (BinOpClosure Min.min P) = MetaClosure P :=
  funext λ _ ↦ propext (SupInfClosure_iff_MetaClosure P)

end Distrib
