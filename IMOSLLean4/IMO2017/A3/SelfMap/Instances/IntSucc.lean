/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Empty
import IMOSLLean4.IMO2017.A3.SelfMap.Irreducible.Basic
import Mathlib.Dynamics.PeriodicPts
import Mathlib.Data.Int.SuccPred

/-!
# `Int.succ`

Let `f : α → α` be an arbitrary self-map.
We show that if `f` has a homomorphism to `Int.succ : ℤ → ℤ`,
  then `f` has no periodic points.
Conversely, if `f` is irreducible and `f` has no periodic points,
  then there is a homomorphism from `f` to `Int.succ`.

While irreducibility is not strictly necessary, lifting it would
  require us to look at the irreducible components of `f`.
This is deferred to `SelfMap/Instances/Main.lean`, which classifies
  a self-map as either having a homomorphism to `Int.succ` or
  having a core structure consisting of coproducts of `FinMap`.
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

/-- `Int.succ` is irreducible. -/
theorem IntSucc_is_irreducible : irreducible Int.succ := λ k m ↦ by
  wlog h : k ≤ m
  · exact (this m k (Int.le_of_not_le h)).symm
  refine ⟨(m - k).natAbs, 0, ?_⟩
  rw [Int.succ_iterate, Int.natAbs_of_nonneg (Int.sub_nonneg_of_le h),
    add_sub_cancel'_right, iterate_zero, id_eq]

/-- If `f → Int.succ`, then `f` has no periodic points. -/
lemma nonperiodic_of_toIntSucc (e : Hom f Int.succ) : f.periodicPts = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr λ x h ↦ by
    rcases h with ⟨n, h, h0⟩
    apply absurd (congr_arg e h0)
    rw [Hom.semiconj_iterate_apply, Int.succ_iterate, add_right_eq_self]
    exact Int.ofNat_ne_zero.mpr h.ne.symm





open scoped Classical

section

variable {f : α → α} (h : irreducible f) (h0 : f.periodicPts = ∅)

lemma exists_Int_grade_of_nonperiodic (x y : α) :
    ∃ n : ℤ, ∀ k m : ℕ, f^[k] x = f^[m] y → (k : ℤ) - m = n := by
  rcases h x y with ⟨k₀, m₀, h⟩
  refine ⟨k₀ - m₀, λ k m h1 ↦ ?_⟩
  rw [sub_eq_sub_iff_add_eq_add, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj]
  refine iterate_injective_of_nonperiod h0 x (?_ : f^[_] x = f^[_] x)
  rw [add_comm, f.iterate_add_apply, h1, add_comm,
    f.iterate_add_apply, Commute.iterate_iterate_self, h]

noncomputable def relative_Int_grade (x y : α) : ℤ :=
  Classical.choose (exists_Int_grade_of_nonperiodic h h0 x y)

lemma relative_Int_grade_spec (h1 : f^[k] x = f^[m] y) :
    (k : ℤ) - m = relative_Int_grade h h0 x y :=
  Classical.choose_spec (exists_Int_grade_of_nonperiodic h h0 x y) k m h1

lemma relative_Int_grade_apply_map (x y : α) :
    relative_Int_grade h h0 x (f y) = relative_Int_grade h h0 x y + 1 := by
  rcases h x y with ⟨k, m, h1⟩
  rw [← relative_Int_grade_spec h h0 h1,
    ← add_sub_right_comm, ← Nat.cast_succ, eq_comm]
  refine relative_Int_grade_spec h h0 ?_
  rw [f.iterate_succ_apply', h1, Commute.self_iterate f]

noncomputable def relative_Int_grade_Hom (x : α) : Hom f Int.succ where
  toFun := relative_Int_grade h h0 x
  Semiconj := relative_Int_grade_apply_map h h0 x

end





/-- `f → Int.succ` iff `f` has no periodic points. -/
theorem toIntSucc_Nonempty_iff {f : α → α} (hf : irreducible f) :
    Nonempty (Hom f Int.succ) ↔ f.periodicPts = ∅ :=
  ⟨λ h ↦ h.elim nonperiodic_of_toIntSucc,
  λ h ↦ (isEmpty_or_nonempty α).elim (λ h0 ↦ ⟨Hom_ofIsEmpty h0 _ _⟩)
    (λ h0 ↦ h0.elim λ x ↦ ⟨relative_Int_grade_Hom hf h x⟩)⟩
