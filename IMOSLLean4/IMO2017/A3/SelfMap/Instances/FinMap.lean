/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic
import IMOSLLean4.IMO2017.A3.SelfMap.PtEquiv.IrredComponent
import Mathlib.Dynamics.PeriodicPts

/-!
# `FinMap`

For any `n : ℕ`, we denote by `FinMap n` the
  self-map on `Fin (n + 1)` defined by `x ↦ x + 1`.
It is an irreducible map.

Let `f : α → α` be an arbitrary self-map.
Every core structure of `FinMap n` over `f` gives an element of period `n + 1`.
Conversely, if `f` is irreducible, then every `x : α` of period `n + 1`
  induces a core structure of `FinMap n` over `f`, sending `0` to `x`.
Thus, when `f` is irreducible, it has a `FinMap n` as a
  core for some `n : ℕ` if and only if `f` has a periodic point.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

open Function

/-- The map `x ↦ x + 1` on `Fin n.succ`. -/
abbrev FinMap (n : ℕ) (k : Fin n.succ) : Fin n.succ := k + 1

lemma FinMap_iterate_Nat (m : Fin n.succ) :
    ∀ k, (FinMap n)^[k] m = m + (k : Fin n.succ)
  | 0 => by rw [Nat.cast_zero, add_zero]; rfl
  | k + 1 => by rw [iterate_succ_apply', FinMap_iterate_Nat m,
                  Nat.cast_succ, ← add_assoc]

lemma FinMap_iterate_eq_self_iff (m : Fin n.succ) :
    (FinMap n)^[k] m = m ↔ n.succ ∣ k := by
  rw [FinMap_iterate_Nat, add_right_eq_self, Fin.nat_cast_eq_zero]

/-- `FinMap n` is irreducible for any `n : ℕ`. -/
theorem FinMap_is_irreducible (n : ℕ) : irreducible (FinMap n) :=
  λ k m ↦ ⟨m, k, by rw [FinMap_iterate_Nat, FinMap_iterate_Nat,
    Fin.cast_val_eq_self, Fin.cast_val_eq_self, add_comm]⟩





/-! ### Periodic points and core instances of `FinMap n` -/

lemma period_of_FinMap_core (C : Core f (FinMap n)) (m : Fin n.succ) :
    f.minimalPeriod (C.ι m) = n.succ :=
  Nat.dvd_right_iff_eq.mp λ k ↦ by
    rw [← isPeriodicPt_iff_minimalPeriod_dvd, IsPeriodicPt, IsFixedPt,
      ← FinMap_iterate_eq_self_iff m, ← C.ι.semiconj_iterate_apply]
    exact C.ι_injective.eq_iff

/-- Homomorphism from `FinMap` defined by a periodic point -/
def FinMapHom (f : α → α) (hx : f.minimalPeriod x = Nat.succ n) :
    Hom (FinMap n) f where
  toFun := λ k ↦ f^[k] x
  Semiconj := λ k ↦ by
    change f^[(k + 1 % _) % _] x = f (f^[k] x)
    rw [Nat.add_mod_mod, ← f.iterate_succ_apply',
      eq_comm, ← iterate_mod_minimalPeriod_eq, hx]


section

open scoped Classical

variable {f : α → α} (hf : irreducible f) (hx : f.minimalPeriod x = Nat.succ n)

lemma periodicPt_exists_iterate_eq (y : α) : ∃ k, f^[k] y = x := by
  rcases hf x y with ⟨u, v, h⟩; refine ⟨n * u + v, ?_⟩
  rw [iterate_add_apply, ← h, ← iterate_add_apply, ← Nat.succ_mul,
    ← iterate_mod_minimalPeriod_eq, hx, Nat.mul_mod_right]; rfl

noncomputable def dist_to_periodicPt (y : α) :=
  Nat.find (periodicPt_exists_iterate_eq hf hx y)

lemma dist_to_periodicPt_eq_zero_iff :
    dist_to_periodicPt hf hx y = 0 ↔ y = x :=
  Nat.find_eq_zero _

lemma dist_to_periodicPt_eq_iff :
    dist_to_periodicPt hf hx y = m ↔
      f^[m] y = x ∧ ∀ k, k < m → f^[k] y ≠ x :=
  Nat.find_eq_iff _

lemma dist_to_periodicPt_apply_of_dist_eq_succ
    (hy : dist_to_periodicPt hf hx y = Nat.succ k) :
    dist_to_periodicPt hf hx (f y) = k := by
  rw [dist_to_periodicPt_eq_iff] at hy ⊢
  exact hy.imp_right λ h k' h0 ↦ h _ (Nat.succ_lt_succ h0)

lemma dist_to_periodicPt_apply_self :
    dist_to_periodicPt hf hx (f x) = n := by
  have h : x ∈ f.periodicPts :=
    minimalPeriod_pos_iff_mem_periodicPts.mp (hx ▸ n.succ_pos)
  rw [dist_to_periodicPt_eq_iff, ← iterate_succ_apply]
  rw [minimalPeriod, dif_pos h] at hx
  refine ⟨hx ▸ (Nat.find_spec h).2, λ k h0 ↦ ?_⟩
  have h1 := Nat.find_min h ((Nat.succ_lt_succ h0).trans_eq hx.symm)
  exact not_and.mp h1 k.succ_pos

lemma dist_to_periodicPt_Fin_apply (y : α) :
    (dist_to_periodicPt hf hx (f y) : Fin n.succ) + 1
      = dist_to_periodicPt hf hx y := by
  rcases (dist_to_periodicPt hf hx y).eq_zero_or_eq_succ_pred with h | h
  ---- Case 1: `y = x`
  · rw [h, Nat.cast_zero, (dist_to_periodicPt_eq_zero_iff hf hx).mp h,
      dist_to_periodicPt_apply_self, Fin.cast_nat_eq_last, Fin.last_add_one]
  ---- Case 2: `y ≠ x`
  · rw [h, dist_to_periodicPt_apply_of_dist_eq_succ _ _ h, Nat.cast_succ]

lemma dist_to_periodicPt_Fin_iterate (y : α) :
    ∀ k, (dist_to_periodicPt hf hx (f^[k] y) : Fin n.succ) + k
      = dist_to_periodicPt hf hx y
  | 0 => by rw [Nat.cast_zero, add_zero]; rfl
  | k + 1 => by rw [iterate_succ_apply, Nat.cast_succ, ← add_assoc,
      dist_to_periodicPt_Fin_iterate _ k, dist_to_periodicPt_Fin_apply]

lemma dist_to_periodicPt_Fin_iterate_self (k : ℕ) :
    (dist_to_periodicPt hf hx (f^[k] x) : Fin n.succ) = -(k : Fin n.succ) := by
  rw [eq_neg_iff_add_eq_zero, dist_to_periodicPt_Fin_iterate,
    (dist_to_periodicPt_eq_zero_iff hf hx).mpr rfl, Nat.cast_zero]

noncomputable def periodicPtHom : Hom f (FinMap n) where
  toFun := λ y ↦ -(dist_to_periodicPt hf hx y)
  Semiconj := λ y ↦ by
    rw [FinMap, eq_neg_add_iff_add_eq, add_neg_eq_iff_eq_add, add_comm]
    exact (dist_to_periodicPt_Fin_apply hf hx y).symm

noncomputable def FinMapCore_of_periodicPt : Core f (FinMap n) where
  φ := periodicPtHom hf hx
  ι := FinMapHom f hx
  is_inv := λ k ↦ by
    change -(dist_to_periodicPt hf hx (f^[k] x) : Fin n.succ) = k
    rw [dist_to_periodicPt_Fin_iterate_self, neg_neg]
    exact k.cast_val_eq_self

end



/-- `FinMap n` is a core of `f` iff there is an element of `f`-period `n + 1`.
  An explicit but noncomputable equivalence should be possible,
  but I don't have time to formalize it right now. -/
theorem FinMapCore_fixed_size_Nonempty_iff (hf : irreducible f) :
    Nonempty (Core f (FinMap n)) ↔ ∃ x, f.minimalPeriod x = n.succ :=
  ⟨λ h ↦ h.elim λ C ↦ ⟨C.ι 0, period_of_FinMap_core C 0⟩,
  λ h ↦ h.elim λ _ hx ↦ ⟨FinMapCore_of_periodicPt hf hx⟩⟩

/-- `FinMap n` is a core of `f` for some `n` iff `f` has a periodic element. -/
theorem FinMapCore_Nonempty_iff (hf : irreducible f) :
    (∃ n, Nonempty (Core f (FinMap n))) ↔ f.periodicPts.Nonempty := by
  simp_rw [FinMapCore_fixed_size_Nonempty_iff hf]; refine ⟨?_, ?_⟩
  · rintro ⟨n, x, h⟩; exact ⟨x, n.succ, n.succ_pos,
      h ▸ isPeriodicPt_minimalPeriod f x⟩
  · rintro ⟨x, h⟩; exact ⟨(f.minimalPeriod x).pred, x,
      (Nat.succ_pred_eq_of_pos (minimalPeriod_pos_of_mem_periodicPts h)).symm⟩
