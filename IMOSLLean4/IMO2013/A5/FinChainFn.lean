/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# Finite-chain functions

A "finite-chain" function is an injective function
  `f : α → α` such that `α ∖ f(α)` is finite.
We prove some properties of finite-chain functions.
-/

namespace IMOSL
namespace IMO2013A5

open Function Finset

structure FinChainFn (f : α → α) where
  injective' : f.Injective
  rangeCompl' : Finset α
  rangeCompl_spec' : (rangeCompl' : Set α) = (Set.range f)ᶜ



namespace FinChainFn

section General

variable {f : α → α} (h : FinChainFn f)
include h

theorem injective : f.Injective := h.injective'

def rangeCompl : Finset α := h.rangeCompl'

theorem rangeCompl_spec : (h.rangeCompl : Set α) = (Set.range f)ᶜ :=
  h.rangeCompl_spec'

theorem mem_rangeCompl_iff : a ∈ h.rangeCompl ↔ a ∉ Set.range f :=
  Set.ext_iff.mp h.rangeCompl_spec a

theorem surjective_iff : f.Surjective ↔ h.rangeCompl = ∅ := by
  rw [← Set.range_eq_univ, ← compl_inj_iff,
    ← h.rangeCompl_spec, Set.compl_univ, coe_eq_empty]

theorem iter_apply_ne_of_mem_rangeCompl_iter_ne (h0 : m ≠ n)
    (h1 : a ∈ h.rangeCompl) (h2 : b ∈ h.rangeCompl) : f^[m] a ≠ f^[n] b := by
  wlog h3 : m < n
  · exact (this h h0.symm h2 h1 <| (le_of_not_gt h3).lt_of_ne h0.symm).symm
  -- Solve assuming `m < n`
  rcases Nat.exists_eq_add_of_le h3.le with ⟨k, rfl⟩
  rw [Nat.lt_add_right_iff_pos] at h3
  rw [f.iterate_add_apply m k b, (h.injective.iterate m).ne_iff]
  rintro rfl; rw [mem_rangeCompl_iff, Set.mem_range] at h1
  refine h1 ⟨f^[k.pred] b, ?_⟩
  rw [← f.iterate_succ_apply', Nat.succ_pred_eq_of_pos h3]

theorem iter_injective (h0 : a ∈ h.rangeCompl) (h1 : b ∈ h.rangeCompl)
    (h2 : f^[m] a = f^[n] b) : m = n ∧ a = b :=
  (eq_or_ne m n).elim
    (λ h3 ↦ ⟨h3, h.injective.iterate n <| by rw [← h2, h3]⟩)
    (λ h3 ↦ absurd h2 (h.iter_apply_ne_of_mem_rangeCompl_iter_ne h3 h0 h1))

theorem iter_eq_iff (h0 : a ∈ h.rangeCompl) (h1 : b ∈ h.rangeCompl) :
    f^[m] a = f^[n] b ↔ m = n ∧ a = b :=
  ⟨h.iter_injective h0 h1, λ h2 ↦ congr_arg₂ _ h2.1 h2.2⟩

end General



section Decidable

variable [DecidableEq α] {f : α → α} (h : FinChainFn f)

def exactIterRange (n : ℕ) : Finset α := h.rangeCompl.image f^[n]

theorem exactIterRange_def (n : ℕ) : h.exactIterRange n = h.rangeCompl.image f^[n] := rfl

theorem mem_exactIterRange_iff : a ∈ h.exactIterRange n ↔ ∃ b ∈ h.rangeCompl, f^[n] b = a :=
  mem_image

theorem exactIterRange_spec (n : ℕ) :
    (h.exactIterRange n : Set α) = Set.range f^[n] \ Set.range f^[n + 1] :=
  Set.ext λ a ↦ by
    rw [exactIterRange, coe_image, h.rangeCompl_spec, iterate_succ,
      Set.range_comp _ f, Set.range_diff_image (h.injective.iterate n)]

theorem exactIterRange_zero : h.exactIterRange 0 = h.rangeCompl :=
  image_id

theorem exactIterRange_disjoint_of_ne (h0 : m ≠ n) :
    Disjoint (h.exactIterRange m) (h.exactIterRange n) :=
  disjoint_iff_ne.mpr λ a h1 b h2 ↦ by
    rw [h.mem_exactIterRange_iff] at h1 h2
    rcases h1 with ⟨a, h1, rfl⟩
    rcases h2 with ⟨b, h2, rfl⟩
    exact h.iter_apply_ne_of_mem_rangeCompl_iter_ne h0 h1 h2

theorem exactIterRange_pairwiseDisjoint (S : Set ℕ) :
    S.PairwiseDisjoint h.exactIterRange :=
  λ _ _ _ _ ↦ h.exactIterRange_disjoint_of_ne

theorem exactIterRange_card (n : ℕ) :
    (h.exactIterRange n).card = h.rangeCompl.card :=
  h.rangeCompl.card_image_of_injective (h.injective.iterate n)

def iterRangeCompl (n : ℕ) : Finset α := (range n).biUnion h.exactIterRange

theorem iterRangeCompl_eq (n : ℕ) :
    h.iterRangeCompl n = (range n).disjiUnion _ (h.exactIterRange_pairwiseDisjoint _) :=
  ((range n).disjiUnion_eq_biUnion _ _).symm

theorem iterRangeCompl_zero : h.iterRangeCompl 0 = ∅ := rfl

theorem iterRangeCompl_succ (n : ℕ) :
    h.iterRangeCompl n.succ = h.exactIterRange n ∪ h.iterRangeCompl n :=
  (congr_arg₂ _ range_succ rfl).trans biUnion_insert

theorem iterRangeCompl_spec :
    ∀ n, (h.iterRangeCompl n : Set α) = (Set.range f^[n])ᶜ
  | 0 => by rw [iterRangeCompl_zero, coe_empty,
              iterate_zero, Set.range_id, Set.compl_univ]
  | n + 1 => by
      rw [h.iterRangeCompl_succ, coe_union, iterRangeCompl_spec n,
        h.exactIterRange_spec, Set.diff_eq, Set.inter_union_distrib_right,
        Set.union_compl_self, Set.univ_inter, ← Set.compl_inter]
      exact congrArg _ (Set.inter_eq_left.mpr λ x ⟨y, h1⟩ ↦ ⟨f y, h1⟩)

theorem iterRangeCompl_one : h.iterRangeCompl 1 = h.rangeCompl :=
  (h.iterRangeCompl_succ 0).trans <| (union_empty _).trans h.exactIterRange_zero

theorem mem_iterRangeCompl_iff : a ∈ h.iterRangeCompl n ↔ a ∉ Set.range f^[n] :=
  Set.ext_iff.mp (h.iterRangeCompl_spec n) a

theorem iterRangeCompl_subset_succ (n : ℕ) : h.iterRangeCompl n ⊆ h.iterRangeCompl (n + 1) :=
  h.iterRangeCompl_succ n ▸ subset_union_right

theorem iterRangeCompl_subset_of_le (h0 : m ≤ n) : h.iterRangeCompl m ⊆ h.iterRangeCompl n :=
  Nat.le_induction Subset.rfl (λ n _ h0 ↦ h0.trans (h.iterRangeCompl_subset_succ n)) n h0

theorem iterRangeCompl_disjoint_exactIterRange (h0 : m ≤ n) :
    Disjoint (h.exactIterRange n) (h.iterRangeCompl m) :=
  (disjoint_biUnion_right _ _ _).mpr
    λ _ h1 ↦ h.exactIterRange_disjoint_of_ne ((mem_range.mp h1).trans_le h0).ne.symm

theorem iterRangeCompl_card : ∀ n, (h.iterRangeCompl n).card = n * h.rangeCompl.card
  | 0 => card_empty.trans h.rangeCompl.card.zero_mul.symm
  | n + 1 => by
      have h0 := card_union_of_disjoint (h.iterRangeCompl_disjoint_exactIterRange n.le_refl)
      rw [h.iterRangeCompl_succ, h0, h.exactIterRange_card,
        iterRangeCompl_card n, Nat.succ_mul, add_comm]

theorem iter_range_of_rangeCompl_singleton (h0 : h.rangeCompl = {a}) :
    ∀ n, h.iterRangeCompl n = (range n).image (λ k ↦ f^[k] a)
  | 0 => rfl
  | n + 1 => by rw [h.iterRangeCompl_succ, exactIterRange, h0, image_singleton,
      iter_range_of_rangeCompl_singleton h0 n, range_succ, image_insert]; rfl

end Decidable
