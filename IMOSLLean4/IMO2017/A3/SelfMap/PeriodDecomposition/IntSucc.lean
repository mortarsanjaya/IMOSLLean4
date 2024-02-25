/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic
import IMOSLLean4.IMO2017.A3.SelfMap.PtEquiv.Quot
import Mathlib.Dynamics.PeriodicPts
import Mathlib.Data.Int.SuccPred

/-!
# Homomorphism to `Int.succ`

Let `f : α → α` be an arbitrary self-map.
We show that `f` has a homomorphism to `Int.succ : ℤ → ℤ`
  if and only if `f` has no periodic points.
-/

namespace IMOSL
namespace IMO2017A3

open Function

/-- An extra lemma -/
lemma iterate_injective_of_nonperiod {f : α → α} (h : f.periodicPts = ∅) (x) :
    Injective (f^[·] x) := λ k m (h0 : f^[k] x = f^[m] x) ↦ by
  wlog h1 : k ≤ m
  · exact (this h x m k h0.symm (Nat.le_of_not_ge h1)).symm
  rcases Nat.exists_eq_add_of_le h1 with ⟨r, rfl⟩
  rw [Nat.add_comm, iterate_add_apply, eq_comm] at h0
  apply IsPeriodicPt.minimalPeriod_dvd at h0
  rw [minimalPeriod_eq_zero_of_nmem_periodicPts (h ▸ Set.not_mem_empty _)] at h0
  rw [Nat.zero_dvd.mp h0, Nat.add_zero]





namespace SelfMap

/-- If `f → Int.succ`, then `f` has no periodic points. -/
lemma nonperiodic_of_toIntSucc (e : Hom f Int.succ) : f.periodicPts = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr λ x h ↦ by
    rcases h with ⟨n, h, h0⟩
    apply absurd (congr_arg e h0)
    rw [Hom.semiconj_iterate_apply, Int.succ_iterate, add_right_eq_self]
    exact Int.ofNat_ne_zero.mpr h.ne.symm





open scoped Classical

section

variable {f : α → α} (h : f.periodicPts = ∅)

lemma exists_Int_grade_of_nonperiodic' (h0 : ptEquiv f x y) :
    ∃ n : ℤ, ∀ k m : ℕ, f^[k] x = f^[m] y → n = k - m := by
  rcases h0 with ⟨k₀, m₀, h0⟩
  refine ⟨k₀ - m₀, λ k m h1 ↦ ?_⟩
  rw [sub_eq_sub_iff_add_eq_add, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj]
  refine iterate_injective_of_nonperiod h x (?_ : f^[_] x = f^[_] x)
  rw [add_comm, f.iterate_add_apply, h0, add_comm,
    f.iterate_add_apply, Commute.iterate_iterate_self, h1]

lemma exists_Int_grade_of_nonperiodic (x : α) :
    ∃ n : ℤ, ∀ k m : ℕ, f^[k] (ptEquiv.eltRep f x) = f^[m] x → n = k - m :=
  exists_Int_grade_of_nonperiodic' h (ptEquiv.eltRep_equiv_self f x)

/-- An absolute grade of each point defined using relative grading to
  a fixed representative of its equivalence class w.r.t. irreducibility. -/
noncomputable def absolute_Int_grade (x : α) : ℤ :=
  Classical.choose (exists_Int_grade_of_nonperiodic h x)

lemma absolute_Int_grade_spec (h0 : f^[k] (ptEquiv.eltRep f x) = f^[m] x) :
    absolute_Int_grade h x = k - m :=
  Classical.choose_spec (exists_Int_grade_of_nonperiodic h x) k m h0

lemma absolute_Int_grade_apply_map (x : α) :
    absolute_Int_grade h (f x) = absolute_Int_grade h x + 1 := by
  rcases ptEquiv.eltRep_equiv_self f x with ⟨m, k, h0⟩
  rw [absolute_Int_grade_spec h h0, ← add_sub_right_comm, ← Nat.cast_succ]
  refine absolute_Int_grade_spec h ?_
  rw [← f.iterate_succ_apply, f.iterate_succ_apply',
    f.iterate_succ_apply', ptEquiv.eltRep_apply_eq, h0]

noncomputable def absolute_Int_grade_Hom : Hom f Int.succ where
  toFun := absolute_Int_grade h
  Semiconj := absolute_Int_grade_apply_map h

end





/-- `f → Int.succ` iff `f` has no periodic points. -/
theorem toIntSucc_Nonempty_iff {f : α → α} :
    Nonempty (Hom f Int.succ) ↔ f.periodicPts = ∅ :=
  ⟨λ h ↦ h.elim nonperiodic_of_toIntSucc, λ h ↦ ⟨absolute_Int_grade_Hom h⟩⟩
