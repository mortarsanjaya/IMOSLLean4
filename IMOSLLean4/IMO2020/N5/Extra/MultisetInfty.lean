/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Set.Finite
import Mathlib.Algebra.BigOperators.Order

namespace IMOSL
namespace IMO2020N5
namespace Multiset

open scoped Classical

variable {S : Set (Multiset α)}

lemma subset_powerset_of_finset_mem_of_count_bdd_fn
    {A : Finset α} (h : ∀ a, (a ∈ A ↔ ∃ M ∈ S, a ∈ M))
    {n : α → ℕ} (h0 : ∀ a, ∀ M ∈ S, M.count a ≤ n a) :
    S ⊆ (A.sum λ a ↦ Multiset.replicate (n a) a).powerset.toFinset := by
  intro M h1
  rw [Finset.mem_coe, Multiset.mem_toFinset,
    Multiset.mem_powerset, Multiset.le_iff_count]
  intro a; by_cases h2 : a ∈ A
  ---- Case 1: `a ∈ A`
  · apply (h0 a M h1).trans
    rw [Multiset.count_sum', ← Multiset.count_replicate_self a (n a)]
    exact Finset.single_le_sum (λ _ _ ↦ Nat.zero_le _) h2
      (f := λ x ↦ (Multiset.replicate (n x) x).count a)
  ---- Case 2: `a ∉ A`
  · exact (Nat.zero_le _).trans_eq' <| Multiset.count_eq_zero.mpr <|
      not_and.mp (not_exists.mp (mt (h a).mpr h2) M) h1

lemma finite_of_finset_mem_of_count_bdd_fn
    {A : Finset α} (h : ∀ a, (a ∈ A ↔ ∃ M ∈ S, a ∈ M))
    {n : α → ℕ} (h0 : ∀ a, ∀ M ∈ S, M.count a ≤ n a) : S.Finite :=
  Set.Finite.subset (Finset.finite_toSet _)
    (subset_powerset_of_finset_mem_of_count_bdd_fn h h0)

lemma finite_of_finite_mem_of_count_bdd
    (h : {a | ∃ M ∈ S, a ∈ M}.Finite) (h0 : ∀ a, ∃ n, ∀ M ∈ S, M.count a ≤ n) :
    S.Finite :=
  (Classical.axiomOfChoice h0).elim λ _ ↦
    finite_of_finset_mem_of_count_bdd_fn (λ _ ↦ h.mem_toFinset)

lemma finite_mem_of_finite (h : S.Finite) : {a | ∃ M ∈ S, a ∈ M}.Finite :=
  (h.toFinset.sum id).toFinset.finite_toSet.subset λ a ↦ by
    rw [Finset.mem_coe, Multiset.mem_toFinset, Finset.mem_sum]
    simp_rw [h.mem_toFinset]; exact id

lemma count_bdd_of_finite (h : S.Finite) (a : α) :
    ∃ n, ∀ M ∈ S, M.count a ≤ n :=
  ⟨Multiset.card (h.toFinset.sum id), λ M h0 ↦ (M.count_le_card a).trans <| by
    rw [map_sum]; exact Finset.single_le_sum
      (λ K _ ↦ K.card.zero_le) (h.mem_toFinset.mpr h0)⟩

lemma finite_iff_finite_mem_and_count_bdd :
    S.Finite ↔ {a | ∃ M ∈ S, a ∈ M}.Finite ∧
      ∀ a, ∃ n, ∀ M ∈ S, M.count a ≤ n :=
  ⟨λ h ↦ ⟨finite_mem_of_finite h, count_bdd_of_finite h⟩,
  λ h ↦ finite_of_finite_mem_of_count_bdd h.1 h.2⟩

lemma infinite_iff_infinite_mem_or_exists_count_not_bdd :
    S.Infinite ↔ {a | ∃ M ∈ S, a ∈ M}.Infinite ∨
      ∃ a, ∀ n, ∃ M ∈ S, n < M.count a := by
  rw [Set.Infinite, finite_iff_finite_mem_and_count_bdd, not_and_or]
  simp only [not_forall, not_exists, not_imp, not_le]; rfl
