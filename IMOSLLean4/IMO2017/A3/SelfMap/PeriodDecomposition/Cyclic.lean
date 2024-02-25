/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Instances.FinMap
import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Sigma
import IMOSLLean4.IMO2017.A3.SelfMap.PtEquiv.Quot

/-
# Cyclic self-maps

Let `f : α → α` be an arbitrary self-map.
We say that `f` is cyclic iff every element is
  point-equivalent to an `f`-periodic element.
We show that every cyclic self-map admits a core of form
  `Σ_{n ∈ S} FinMap n` for some subset `S ⊆ ℕ`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

open Function ptEquiv
open scoped Classical

abbrev in_cyclicComponent (f : α → α) (x : α) :=
  ∃ y : α, ptEquiv f y x ∧ y ∈ f.periodicPts

def cyclic (f : α → α) := ∀ x : α, in_cyclicComponent f x



namespace cyclic

variable {f : α → α} (h : cyclic f)

/-! #### Periodic representative under point-equivalence -/

section

variable (s : Quotient (mkSetoid f))

lemma exists_ptEquiv_periodic_rep :
    ∃ y, mkQuotient f y = s ∧ y ∈ f.periodicPts :=
  (h (quotientRep s)).elim λ y ⟨h, h0⟩ ↦ ⟨y, rep_eq_quotient_iff.mpr h, h0⟩

noncomputable def ptEquivRep :=
  Classical.choose (exists_ptEquiv_periodic_rep h s)

lemma ptEquivRep_is_rep : mkQuotient f (ptEquivRep h s) = s :=
  (Classical.choose_spec (exists_ptEquiv_periodic_rep h s)).1

lemma ptEquivRep_is_periodic : ptEquivRep h s ∈ f.periodicPts :=
  (Classical.choose_spec (exists_ptEquiv_periodic_rep h s)).2

lemma ptEquivRep_is_periodic' :
    ∃ n : ℕ, f.minimalPeriod (ptEquivRep h s) = n.succ :=
  ⟨Nat.pred _, Eq.symm <| Nat.succ_pred_eq_of_pos <|
    minimalPeriod_pos_of_mem_periodicPts <| ptEquivRep_is_periodic h s⟩

noncomputable def ptEquivRep_periodPred :=
  Classical.choose (ptEquivRep_is_periodic' h s)

lemma ptEquivRep_periodPred_spec :
    f.minimalPeriod (ptEquivRep h s) = (ptEquivRep_periodPred h s).succ :=
  Classical.choose_spec (ptEquivRep_is_periodic' h s)

lemma ptEquivRep_periodPred_iterate_succ :
    f^[(ptEquivRep_periodPred h s).succ] (ptEquivRep h s) = ptEquivRep h s :=
  ptEquivRep_periodPred_spec h s ▸ iterate_minimalPeriod

lemma iterate_succ_of_lt_ptEquivRep_periodPred
    (h0 : n < ptEquivRep_periodPred h s) :
    f^[n.succ] (ptEquivRep h s) ≠ ptEquivRep h s :=
  not_isPeriodicPt_of_pos_of_lt_minimalPeriod n.succ_ne_zero <|
    ptEquivRep_periodPred_spec h s ▸ Nat.succ_lt_succ h0

end





/-! #### Dense `FinMap` core structure of cyclic self-maps -/

lemma ptEquivRep_exists_iterate_eq (y : α) :
    ∃ k, f^[k] y = ptEquivRep h (mkQuotient f y) := by
  let s := mkQuotient f y
  obtain ⟨k, m, h0⟩ : ptEquiv f y (ptEquivRep h s) :=
    mkQuotient_eq_iff.mp (ptEquivRep_is_rep _ _).symm
  refine ⟨ptEquivRep_periodPred h s * m + k, ?_⟩
  rw [iterate_add_apply, h0, ← iterate_add_apply,
    ← Nat.succ_mul, ← ptEquivRep_periodPred_spec]
  exact (isPeriodicPt_minimalPeriod f _).mul_const m

noncomputable def ptEquivRep_dist (x : α) : ℕ :=
  Nat.find (ptEquivRep_exists_iterate_eq h x)

lemma ptEquivRep_dist_eq_zero_iff :
    ptEquivRep_dist h x = 0 ↔ x = ptEquivRep h (mkQuotient f x) :=
  Nat.find_eq_zero _

lemma ptEquivRep_dist_of_rep (s) : ptEquivRep_dist h (ptEquivRep h s) = 0 :=
  (ptEquivRep_dist_eq_zero_iff h).mpr <|
    congr_arg _ (ptEquivRep_is_rep h s).symm

lemma ptEquivRep_dist_eq_iff :
    ptEquivRep_dist h x = m ↔ f^[m] x = ptEquivRep h (mkQuotient f x) ∧
      ∀ k, k < m → f^[k] x ≠ ptEquivRep h (mkQuotient f x) :=
  Nat.find_eq_iff _

lemma ptEquivRep_dist_eq_succ_imp_apply (h0 : ptEquivRep_dist h x = n.succ) :
    ptEquivRep_dist h (f x) = n := by
  rw [ptEquivRep_dist_eq_iff, mkQuotient_apply_eq]
  exact ((ptEquivRep_dist_eq_iff h).mp h0).imp_right
    λ h0 k h1 ↦ h0 _ (Nat.succ_lt_succ h1)

lemma ptEquivRep_dist_apply_rep (s : Quotient (mkSetoid f)) :
    ptEquivRep_dist h (f (ptEquivRep h s)) = ptEquivRep_periodPred h s := by
  rw [ptEquivRep_dist_eq_iff, mkQuotient_apply_eq, ptEquivRep_is_rep]
  exact ⟨ptEquivRep_periodPred_iterate_succ h s,
    λ k ↦ iterate_succ_of_lt_ptEquivRep_periodPred h s⟩

noncomputable def ptEquivRep_neg_dist_Fin (x : α) (n : ℕ) : Fin n.succ :=
  -ptEquivRep_dist h x

lemma ptEquivRep_neg_dist_Fin_of_rep (s : Quotient (mkSetoid f)) (n : ℕ) :
    ptEquivRep_neg_dist_Fin h (ptEquivRep h s) n = 0 :=
  neg_eq_zero.mpr <| congr_arg Nat.cast (ptEquivRep_dist_of_rep h _)

lemma ptEquivRep_neg_dist_Fin_apply_eq
    (h0 : ptEquivRep_periodPred h (mkQuotient f x) = n) :
    ptEquivRep_neg_dist_Fin h (f x) n = ptEquivRep_neg_dist_Fin h x n + 1 := by
  unfold ptEquivRep_neg_dist_Fin
  rcases (ptEquivRep_dist h x).eq_zero_or_eq_succ_pred with h1 | h1
  ---- Case 1: `x` is a representative
  · nth_rw 1 [(ptEquivRep_dist_eq_zero_iff h).mp h1]
    rw [ptEquivRep_dist_apply_rep, h0, Fin.cast_nat_eq_last,
      Fin.neg_last, h1, Nat.cast_zero, neg_zero, zero_add]
  ---- Case 2: `x` is not a representative
  · rw [ptEquivRep_dist_eq_succ_imp_apply h h1, h1,
      Nat.pred_succ, Nat.cast_succ, neg_add, neg_add_cancel_right]

/-- The inner homomorphism to dense `FinMap` sigma -/
noncomputable def toSigmaFinMapHom :
    Hom f (Sigma.map id λ s ↦ FinMap (ptEquivRep_periodPred h s)) where
  toFun := λ x ↦ ⟨mkQuotient f x, ptEquivRep_neg_dist_Fin h x _⟩
  Semiconj := λ x ↦ by
    simp only [Sigma.map, id_eq]; rw [mkQuotient_apply_eq]
    exact Sigma.ext rfl (heq_of_eq (ptEquivRep_neg_dist_Fin_apply_eq h rfl))

lemma ptEquivRep_neg_dist_Fin_iterate_eq
    (h0 : ptEquivRep_periodPred h (mkQuotient f x) = n) :
    ∀ k, ptEquivRep_neg_dist_Fin h (f^[k] x) n
      = ptEquivRep_neg_dist_Fin h x n + k
  | 0 => (add_zero _).symm
  | k + 1 => by
      rw [f.iterate_succ_apply, Nat.cast_succ, ← add_assoc,
        ptEquivRep_neg_dist_Fin_iterate_eq ?_ k, add_right_comm,
        ptEquivRep_neg_dist_Fin_apply_eq h h0]
      rwa [mkQuotient_apply_eq]

/-- The dense core structure of `FinMap` sigma on `f` -/
noncomputable def SigmaFinMapDenseCore :
    Core f (Sigma.map id λ s ↦ FinMap (ptEquivRep_periodPred h s)) where
  φ := toSigmaFinMapHom h
  ι := Hom.sigma_elim λ s ↦ FinMapHom (ptEquivRep_periodPred_spec h s)
  is_inv := λ p ↦ by
    change ⟨mkQuotient f (f^[_] _), ptEquivRep_neg_dist_Fin h (f^[_] _) _⟩ = p
    rw [mkQuotient_iterate_eq, ptEquivRep_neg_dist_Fin_iterate_eq h rfl,
      ptEquivRep_neg_dist_Fin_of_rep h, zero_add,
      ptEquivRep_is_rep, Fin.cast_val_eq_self]

theorem SigmaFinMapDenseCore_is_dense (x : α) :
    ptEquiv f x ((SigmaFinMapDenseCore h).ι <| (SigmaFinMapDenseCore h).φ x) :=
  mkQuotient_eq_iff.mp
    ((mkQuotient_iterate_eq f _ _).trans <| ptEquivRep_is_rep h _).symm





/-! #### Reduced `FinMap` core structure of cyclic self-maps -/

def periodPred_set : Set ℕ := Set.range (ptEquivRep_periodPred h)

lemma periodPred_set_nonempty (h0 : Nonempty α) : (periodPred_set h).Nonempty :=
  Set.range_nonempty_iff_nonempty.mpr ((nonempty_quotient_iff _).mpr h0)


section

variable (n : periodPred_set h)

noncomputable def periodPred_ptEquivRep := Classical.choose n.2

lemma periodPred_ptEquivRep_spec :
    ptEquivRep_periodPred h (periodPred_ptEquivRep h n) = n.1 :=
  Classical.choose_spec n.2

noncomputable def periodPred_rep : α :=
  ptEquivRep h (periodPred_ptEquivRep h n)

lemma periodPred_rep_spec :
    mkQuotient f (periodPred_rep h n) = periodPred_ptEquivRep h n :=
  ptEquivRep_is_rep h _

lemma ptEquivRep_neg_dist_Fin_of_periodPred_rep (n : periodPred_set h) (m) :
    ptEquivRep_neg_dist_Fin h (periodPred_rep h n) m = 0 :=
  ptEquivRep_neg_dist_Fin_of_rep h _ _

lemma periodPred_rep_minimalPeriod :
    f.minimalPeriod (periodPred_rep h n) = n.1.succ :=
  periodPred_ptEquivRep_spec h n ▸ ptEquivRep_periodPred_spec h _

end



noncomputable def ptEquivRep_toSet (x : α) : periodPred_set h :=
  ⟨ptEquivRep_periodPred h (mkQuotient f x), _, rfl⟩

lemma ptEquivRep_toSet_rep (n : periodPred_set h) :
    ptEquivRep_toSet h (periodPred_rep h n) = n :=
  Subtype.ext <| periodPred_ptEquivRep_spec h n ▸
    congr_arg (ptEquivRep_periodPred h) (periodPred_rep_spec h _)

lemma ptEquivRep_toSet_apply_eq (x : α) :
    ptEquivRep_toSet h (f x) = ptEquivRep_toSet h x :=
  Subtype.ext <| congr_arg (ptEquivRep_periodPred h) (mkQuotient_apply_eq f x)

noncomputable def toSigmaFinMapReducedHom :
    Hom f (Sigma.map id λ n : periodPred_set h ↦ FinMap n) where
  toFun := λ x ↦ ⟨ptEquivRep_toSet h x, ptEquivRep_neg_dist_Fin h x _⟩
  Semiconj := λ x ↦ by
    simp only; rw [ptEquivRep_toSet_apply_eq]
    exact Sigma.ext rfl (heq_of_eq (ptEquivRep_neg_dist_Fin_apply_eq h rfl))

lemma toSigmaFinMapReducedHom_apply_periodPred_rep (n : periodPred_set h) :
    toSigmaFinMapReducedHom h (periodPred_rep h n) = ⟨n, 0⟩ := by
  simp only [toSigmaFinMapReducedHom]
  rw [ptEquivRep_toSet_rep, ptEquivRep_neg_dist_Fin_of_periodPred_rep]

lemma sigma_map_reduced_apply (n : periodPred_set h) (k : Fin n.1.succ) :
    ∀ m, (Sigma.map id λ n : periodPred_set h ↦ FinMap n)^[m] ⟨n, k⟩ = ⟨n, k + m⟩
  | 0 => by rw [Nat.cast_zero, add_zero]; rfl
  | m + 1 => by rw [Nat.cast_succ, ← add_assoc,
      iterate_succ_apply', sigma_map_reduced_apply n k m]; rfl

/-- The reduced core structure of `FinMap` sigma on `f` -/
noncomputable def SigmaFinMapReducedCore :
    Core f (Sigma.map id λ n : periodPred_set h ↦ FinMap n) where
  φ := toSigmaFinMapReducedHom h
  ι := Hom.sigma_elim λ n ↦ FinMapHom (periodPred_rep_minimalPeriod h n)
  is_inv := λ ⟨n, k⟩ ↦ by
    change toSigmaFinMapReducedHom h (f^[k] (periodPred_rep h n)) = _
    rw [(toSigmaFinMapReducedHom h).semiconj_iterate_apply,
      toSigmaFinMapReducedHom_apply_periodPred_rep,
      sigma_map_reduced_apply, zero_add, Fin.cast_val_eq_self]

end cyclic



/-- Nonempty core version of `SigmaFinMapReducedCore` -/
theorem exists_SigmaFinMapReducedCore (h : cyclic f) :
    ∃ S : Set ℕ, Nonempty (Core f (Sigma.map id λ n : S ↦ FinMap n)) :=
  ⟨_, ⟨h.SigmaFinMapReducedCore⟩⟩

/-- Nonempty core version of `SigmaFinMapReducedCore` over nonempty set -/
theorem exists_nonempty_SigmaFinMapReducedCore
    (h : Nonempty α) {f : α → α} (h0 : cyclic f) :
    ∃ S : Set ℕ, S.Nonempty ∧
      Nonempty (Core f (Sigma.map id λ n : S ↦ FinMap n)) :=
  ⟨_, h0.periodPred_set_nonempty h, ⟨h0.SigmaFinMapReducedCore⟩⟩
