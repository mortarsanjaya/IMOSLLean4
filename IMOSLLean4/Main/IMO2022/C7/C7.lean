/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Finset.Order
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Ring.Int

/-!
# IMO 2022 C7

Let $m$ be a positive integer and consider an arbitrary subset $S ⊆ ℤ^m$.
We say that $S$ is *add-sup closed* if $S$ is closed under
  taking pointwise addition and pointwise maximum.
A set $G ⊆ ℤ^m$ is called an *add-sup generator* if
  the only add-sup closed set containing $G$ is $ℤ^m$.
Find the smallest possible size of an add-sup generator, in terms of $m$.
-/

namespace IMOSL
namespace IMO2022C7

/-! ### General theory of closed sets -/

class AddMaxClosed [Add α] [Max α] (S : Set α) : Prop where
  add_mem : ∀ v ∈ S, ∀ w ∈ S, v + w ∈ S
  sup_mem : ∀ v ∈ S, ∀ w ∈ S, v ⊔ w ∈ S


namespace AddMaxClosed

section

variable [Add α] [Max α] {S : Set α} (hS : AddMaxClosed S) (hv : v ∈ S) (hw : w ∈ S)
include hS hv hw

theorem mem_of_add_eq (hx : x = v + w) : x ∈ S :=
  hx ▸ hS.add_mem _ hv _ hw

theorem mem_of_sup_eq (hx : x = v ⊔ w) : x ∈ S :=
  hx ▸ hS.sup_mem _ hv _ hw

end


section

variable [Add α] [SemilatticeSup α] {S : Set α} (hS : AddMaxClosed S)
include hS

theorem Finset_range_sup_mem {f : ℕ → α} (hf : ∀ k, f k ∈ S) :
    ∀ n : ℕ, (Finset.range n.succ).sup' Finset.nonempty_range_succ f ∈ S := by
  refine Nat.rec ?_ λ n hn ↦ ?_
  · simpa only [Finset.range_one, Finset.sup'_singleton] using hf 0
  · simp only [Finset.range_succ (n := n.succ)]
    rw [Finset.sup'_insert Finset.nonempty_range_succ]
    exact hS.sup_mem _ (hf n.succ) _ hn

theorem mem_of_Finset_range_sup_eq {f : ℕ → α} (hf : ∀ k, f k ∈ S) {x : α}
    (hx : x = (Finset.range (n + 1)).sup' Finset.nonempty_range_succ f) : x ∈ S :=
  hx ▸ Finset_range_sup_mem hS hf n

open Fin.NatCast in
theorem Fin_univ_sup_mem {f : Fin (n + 1) → α} (hf : ∀ k, f k ∈ S) :
    Finset.univ.sup' Finset.univ_nonempty f ∈ S := by
  have h : (Finset.range n.succ).image (λ k : ℕ ↦ (k : Fin (n + 1))) = Finset.univ :=
    Finset.eq_univ_of_forall λ k ↦ Finset.mem_image.mpr
      ⟨k.1, Finset.mem_range.mpr k.isLt, k.cast_val_eq_self⟩
  simp only [← h, ← Finset.sup'_comp_eq_image Finset.nonempty_range_succ]
  exact Finset_range_sup_mem hS (λ k ↦ hf k) n

theorem mem_of_Fin_univ_sup_eq {f : Fin (n + 1) → α} (hf : ∀ k, f k ∈ S)
    {x : α} (hx : x = Finset.univ.sup' Finset.univ_nonempty f) : x ∈ S :=
  hx ▸ hS.Fin_univ_sup_mem hf

end


section

variable [Max α] [AddCommMonoid α] {S : Set α} (hS : AddMaxClosed S)
include hS

theorem smul_mem_of_pos (hv : v ∈ S) : ∀ n > 0, n • v ∈ S :=
  Nat.le_induction ((one_nsmul v).symm ▸ hv)
    λ n _ hn ↦ hS.mem_of_add_eq hn hv (succ_nsmul v n)

theorem add_smul_mem (hv : v ∈ S) (hw : w ∈ S) : ∀ n : ℕ, v + n • w ∈ S
  | 0 => by rwa [zero_nsmul, add_zero]
  | n + 1 => hS.add_mem _ hv _ (hS.smul_mem_of_pos hw _ n.succ_pos)

theorem mem_of_add_smul_eq (hv : v ∈ S) (hw : w ∈ S) {n : ℕ} (hx : x = v + n • w) : x ∈ S :=
  hx ▸ hS.add_smul_mem hv hw n

end



/-! ##### Some non-trivial examples of closed sets -/

theorem univ [Add α] [Max α] : AddMaxClosed (Set.univ : Set α) where
  add_mem := λ _ _ _ _ ↦ Set.mem_univ _
  sup_mem := λ _ _ _ _ ↦ Set.mem_univ _

theorem empty [Add α] [Max α] : AddMaxClosed (∅ : Set α) where
  add_mem := λ _ _ _ ↦ id
  sup_mem := λ _ _ _ ↦ id

theorem ofNonnegHalf (i : ι) : AddMaxClosed {v : ι → ℤ | 0 ≤ v i} where
  add_mem := λ _ hv _ hw ↦ Int.add_nonneg hv hw
  sup_mem := λ _ hv _ _ ↦ hv.trans (Int.le_max_left _ _)

theorem ofNonposHalf (i : ι) : AddMaxClosed {v : ι → ℤ | v i ≤ 0} where
  add_mem := λ _ hv _ hw ↦ Int.add_nonpos hv hw
  sup_mem := λ _ hv _ hw ↦ Set.mem_setOf_eq.mpr (sup_le_iff.mpr ⟨hv, hw⟩)

theorem ofSlopedHalf {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (i j : ι) :
    AddMaxClosed {v : ι → ℤ | x * v i ≤ y * v j} where
  add_mem := λ v hv w hw ↦ by
    simp only [Set.mem_setOf_eq, Pi.add_apply, Int.mul_add]
    exact Int.add_le_add hv hw
  sup_mem := λ v hv w hw ↦ by
    simp only [Set.mem_setOf_eq, Pi.sup_apply]
    rw [mul_max_of_nonneg _ _ hx, mul_max_of_nonneg _ _ hy]
    exact max_le_max hv hw

theorem ofPreimage {S : Set (α → ℤ)} (hS : AddMaxClosed S) (i : α → β) :
    AddMaxClosed ((· ∘ i) ⁻¹' S) where
  add_mem := λ _ hv _ hw ↦ hS.add_mem _ hv _ hw
  sup_mem := λ _ hv _ hw ↦ hS.sup_mem _ hv _ hw



/-! ##### Closed sets satisfying certain conditions -/

theorem Nat_Finsupp_mem_of_zero_single_mem [DecidableEq ι] {S : Set (ι → ℤ)}
    (hS : AddMaxClosed S) (hS0 : 0 ∈ S) (hS1 : ∀ i, ⇑(Finsupp.single i 1) ∈ S) :
    ∀ v : ι →₀ ℕ, Nat.cast ∘ v ∈ S := by
  intro v; induction' v using Finsupp.induction_linear with f g hf hg i k
  · exact hS0
  · exact hS.add_mem _ hf _ hg
  · obtain rfl | h : k = 0 ∨ 0 < k := k.eq_zero_or_pos
    · rw [Finsupp.single_zero]; exact hS0
    · have h0 : (Nat.cast : ℕ → ℤ) ∘ ⇑(Finsupp.single i k) = k • ⇑(Finsupp.single i 1) := by
        funext j; rw [Function.comp_apply, Pi.smul_apply, nsmul_eq_mul]
        obtain rfl | h0 : i = j ∨ i ≠ j := eq_or_ne i j
        · rw [Finsupp.single_eq_same, Finsupp.single_eq_same, mul_one]
        · rw [Finsupp.single_eq_of_ne h0, Finsupp.single_eq_of_ne h0, mul_zero]; rfl
      exact h0 ▸ hS.smul_mem_of_pos (hS1 i) k h


section

variable [Fintype ι] [DecidableEq ι] {S : Set (ι → ℤ)}
  (hS : AddMaxClosed S) (hS0 : 0 ∈ S) (hS1 : ∀ i, Pi.single i 1 ∈ S)
include hS hS0 hS1

theorem Nat_mem_of_zero_single_mem (v : ι → ℕ) : Nat.cast ∘ v ∈ S := by
  refine Nat_Finsupp_mem_of_zero_single_mem hS hS0 (λ i ↦ ?_)
    (Finsupp.onFinset Finset.univ v λ _ _ ↦ Finset.mem_univ _)
  rw [Finsupp.single, Finsupp.coe_mk]; convert hS1 i

theorem Int_mem_of_zero_single_mem {v : ι → ℤ} (hf : ∀ i, 0 ≤ v i) : v ∈ S := by
  lift v to ι → ℕ using hf; exact Nat_mem_of_zero_single_mem hS hS0 hS1 v

/-- While `0 ∈ S` is actually unnecessary, we add it for convenience -/
theorem eq_univ_of_neg_one_and_single_mem (hS2 : -1 ∈ S) : S = Set.univ := by
  refine Set.eq_univ_of_forall λ v ↦ ?_
  suffices ∃ (w : ι → ℤ) (n : ℕ), (∀ i, 0 ≤ w i) ∧ n > 0 ∧ v = w + n • -1 by
    rcases this with ⟨w, n, hw, hn, rfl⟩
    exact hS.add_mem _ (hS.Int_mem_of_zero_single_mem hS0 hS1 hw)
      _ (hS.smul_mem_of_pos hS2 _ hn)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i, -v i ≤ N := by
    obtain ⟨N, hN⟩ := (Finset.univ.image λ i ↦ (v i).natAbs).exists_le
    refine ⟨N, λ i ↦ (neg_le_abs _).trans ?_⟩
    rw [← Int.natCast_natAbs, Int.ofNat_le]
    exact hN _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  refine ⟨v - (N + 1) • (-1), N + 1, λ i ↦ ?_, N.succ_pos, (sub_add_cancel _ _).symm⟩
  show 0 ≤ v i - (N + 1) * (-1)
  rw [mul_neg_one, sub_neg_eq_add, ← neg_le_iff_add_nonneg']
  exact Int.le_add_one (hN i)

end

end AddMaxClosed





/-! ### Add-sup generators -/

def AddSupGenerator [Add α] [Max α] (A : Finset α) :=
  ∀ S : Set α, (A : Set α) ⊆ S → AddMaxClosed S → S = Set.univ


namespace AddSupGenerator

lemma univ [Fintype α] [Add α] [Max α] : AddSupGenerator (Finset.univ : Finset α) :=
  λ S hS _ ↦ by rwa [Finset.coe_univ, Set.univ_subset_iff] at hS

lemma ofSubset [Add α] [Max α] {A B : Finset α} (hA : AddSupGenerator A) (hAB : A ⊆ B) :
    AddSupGenerator B :=
  λ S hS ↦ hA S λ _ h ↦ hS (hAB h)

lemma ofEmbedding [DecidableEq α] [Fintype β] [DecidableEq β]
    {A : Finset (α → ℤ)} (hA : AddSupGenerator A) (ι : β ↪ α) :
    AddSupGenerator (A.image λ f ↦ f ∘ ι) := by
  intro S hS hS0
  rw [Finset.coe_image, Set.image_subset_iff] at hS
  specialize hA _ hS (hS0.ofPreimage _)
  have h : (λ f : α → ℤ ↦ f ∘ ι).Surjective := ι.2.surjective_comp_right
  rwa [Set.preimage_eq_univ_iff, Set.range_eq_univ.mpr h, Set.univ_subset_iff] at hA

end AddSupGenerator



/-! ##### Instances of add-sup generators -/

theorem empty_not_AddSupGenerator [Add α] [Max α] [Nonempty α] :
    ¬AddSupGenerator (∅ : Finset α) :=
  λ h ↦ Set.empty_ne_univ (h ∅ (λ _ hf ↦ Set.mem_toFinset.mp hf) AddMaxClosed.empty)

theorem not_AddSupGenerator_of_subset_NonnegHalf
    {S : Finset (ι → ℤ)} (hS : (S : Set (ι → ℤ)) ⊆ {v | 0 ≤ v i}) :
    ¬AddSupGenerator S := by
  intro h; have h0 : -1 ∈ {v : ι → ℤ | 0 ≤ v i} :=
    h _ hS (AddMaxClosed.ofNonnegHalf i) ▸ Set.mem_univ _
  exact (Int.negSucc_not_nonneg 0).mp h0

theorem not_AddSupGenerator_of_subset_NonposHalf
    {S : Finset (ι → ℤ)} (hS : (S : Set (ι → ℤ)) ⊆ {v | v i ≤ 0}) :
    ¬AddSupGenerator S := by
  intro h; have h0 : 1 ∈ {v : ι → ℤ | v i ≤ 0} :=
    h _ hS (AddMaxClosed.ofNonposHalf i) ▸ Set.mem_univ _
  exact (Int.negSucc_not_nonneg 0).mp h0

theorem singleton_not_AddSupGenerator [hι : Nonempty ι] (v : ι → ℤ) :
    ¬AddSupGenerator {v} := by
  intro h; rcases hι with ⟨i⟩
  obtain h0 | h0 : 0 ≤ v i ∨ v i ≤ 0 := le_total _ _
  exacts [not_AddSupGenerator_of_subset_NonnegHalf (Finset.singleton_subset_set_iff.mpr h0) h,
    not_AddSupGenerator_of_subset_NonposHalf (Finset.singleton_subset_set_iff.mpr h0) h]

theorem Fin2_AddSupGenerator : AddSupGenerator {![-1, 1], ![1, -2]} := by
  intro S hS hS0; replace hS : ![-1, 1] ∈ S ∧ ![1, -2] ∈ S := by
    rw [Finset.coe_insert, Finset.coe_singleton] at hS
    exact ⟨hS (Set.mem_insert _ _), hS (Set.mem_insert_of_mem _ rfl)⟩
  have h : ![0, -1] ∈ S := hS0.mem_of_add_eq hS.1 hS.2 (by decide)
  have h0 : ![-1, 0] ∈ S := hS0.mem_of_add_eq h hS.1 (by decide)
  have h1 : Pi.single 1 1 ∈ S := hS0.mem_of_sup_eq h hS.1 (by decide)
  replace hS : ∀ i : Fin 2, Pi.single i 1 ∈ S
    | 1 => h1 | 0 => hS0.mem_of_sup_eq h0 hS.2 (by decide)
  replace h : -1 ∈ S := hS0.mem_of_add_eq h h0 (by decide)
  replace h0 : 1 ∈ S := hS0.mem_of_add_eq (hS 0) (hS 1) (by decide)
  replace h1 : 0 ∈ S := hS0.mem_of_add_eq h h0 (by decide)
  exact AddMaxClosed.eq_univ_of_neg_one_and_single_mem hS0 h1 hS h


section

variable [Fintype ι] [DecidableEq ι] {v w : ι → ℤ} (h : AddSupGenerator {v, w})
include h

omit [DecidableEq ι] in
theorem doubleton_AddSupGenerator_imp₁ (i) : v i * w i < 0 := by
  rw [← not_le, mul_nonneg_iff]
  rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
  -- Case 1: `v_i, w_i ≥ 0`
  · refine not_AddSupGenerator_of_subset_NonnegHalf (i := i) ?_ h
    rw [Finset.coe_insert, Finset.coe_singleton]
    rintro _ (rfl | rfl); exacts [h0, h1]
  -- Case 2: `v_i, w_i ≤ 0`
  · refine not_AddSupGenerator_of_subset_NonposHalf (i := i) ?_ h
    rw [Finset.coe_insert, Finset.coe_singleton]
    rintro _ (rfl | rfl); exacts [h0, h1]

theorem doubleton_AddSupGenerator_imp₂ (h0 : i ≠ j) : v i * v j < 0 := by
  ---- First reduce the problem to the case `v_i > 0`
  wlog hvi : 0 < v i generalizing h v w
  · specialize this (Finset.pair_comm v w ▸ h)
      (pos_of_mul_neg_right (doubleton_AddSupGenerator_imp₁ h i) (not_lt.mp hvi))
    refine neg_of_mul_pos_left ?_ this.le
    rw [mul_mul_mul_comm, mul_pos_iff]
    have h2 := doubleton_AddSupGenerator_imp₁ h
    right; exact ⟨h2 i, h2 j⟩
  ---- Contradiction setup
  refine mul_neg_of_pos_of_neg hvi (lt_of_not_ge λ hvj ↦ ?_)
  replace hvj : 0 < v j :=
    hvj.lt_of_ne λ h1 ↦ (doubleton_AddSupGenerator_imp₁ h j).ne (by rw [← h1, zero_mul])
  have hwi : w i < 0 := neg_of_mul_neg_right (doubleton_AddSupGenerator_imp₁ h i) hvi.le
  have hwj : w j < 0 := neg_of_mul_neg_right (doubleton_AddSupGenerator_imp₁ h j) hvj.le
  ---- Reduce to the case where `v_i w_j ≥ w_i v_j`
  wlog h1 : v j * w i ≤ v i * w j generalizing i j
  · exact this h0.symm hvj hvi hwj hwi (Int.le_of_not_le h1)
  ---- Show contradiction by showing that `{v, w}` is contained in a sloped set
  have h2 : {x : ι → ℤ | v j * x i ≤ v i * x j} = Set.univ := by
    refine h _ ?_ (AddMaxClosed.ofSlopedHalf hvj.le hvi.le i j)
    rw [Finset.coe_insert, Finset.coe_singleton]
    rintro _ (rfl | rfl)
    exacts [Int.le_of_eq (mul_comm _ _), h1]
  replace h2 : Pi.single i 1 ∈ {x : ι → ℤ | v j * x i ≤ v i * x j} := h2 ▸ Set.mem_univ _
  rw [Set.mem_setOf_eq, Pi.single_eq_same, mul_one,
    Pi.single_eq_of_ne h0.symm, mul_zero] at h2
  exact hvj.not_ge h2

end


theorem Fin3_doubleton_not_AddSupGenerator (v w : Fin 3 → ℤ) : ¬AddSupGenerator {v, w} := by
  have X : ∀ i : Fin 3, i ≠ i + 1 := by decide
  intro h; replace h (i) := doubleton_AddSupGenerator_imp₂ h (X i)
  have h0 : (v 0 * v 1) * (v 1 * v 2) * (v 2 * v 0) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (h 0) (h 1)) (h 2)
  rw [mul_mul_mul_comm, mul_rotate (v 0), ← sq] at h0
  exact h0.not_ge (sq_nonneg _)

theorem Fin_general_AddSupGenerator (n : ℕ) :
    AddSupGenerator {-1, λ k ↦ k.1, λ k : Fin (n + 1) ↦ 1 - (k.1 : ℤ) ^ 2} := by
  intro S hS hS0
  ---- First, for any `k`, the vector `d_k(j) = 1 - 2(k - j)^2` belongs in `S`
  rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton, Set.subset_def] at hS
  simp only [Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq] at hS
  rcases hS with ⟨hS, h⟩
  replace h (k : Fin n.succ) : (λ j : Fin n.succ ↦ 1 - (j.1 - k.1 : ℤ) ^ 2) ∈ S := by
    apply hS0.mem_of_add_smul_eq (hS0.add_smul_mem h.2 h.1 (2 * k)) hS (n := k.1 ^ 2)
    funext j; show 1 - (j.1 - k.1 : ℤ) ^ 2 = 1 - j.1 ^ 2 + 2 * k * j + k ^ 2 * -1
    rw [mul_neg_one, ← sub_eq_add_neg, sub_add, sub_sub, sub_sq, Int.mul_right_comm]
  ---- Next, show that `0 ∈ S`
  have h0 : 0 ∈ S := by
    refine hS0.mem_of_add_eq hS (hS0.mem_of_Fin_univ_sup_eq h ?_) (neg_add_cancel _).symm
    funext k; rw [Pi.one_apply, Finset.sup'_apply]
    apply le_antisymm
    exacts [Finset.le_sup'_of_le _ (Finset.mem_univ k) (sub_self (k.1 : ℤ) ▸ Int.le_refl 1),
      Finset.sup'_le Finset.univ_nonempty _ λ j _ ↦ sub_le_self _ (sq_nonneg _)]
  ---- Show that `e_k ∈ S` for each `k`, and finish
  replace h (k) : Pi.single k 1 ∈ S := by
    refine hS0.mem_of_sup_eq h0 (h k) (funext λ j ↦ ?_)
    show Pi.single k 1 j = max 0 (1 - (j.1 - k.1 : ℤ) ^ 2)
    obtain rfl | h1 : k = j ∨ k ≠ j := eq_or_ne k j
    · rw [Pi.single_eq_same, sub_self]; rfl
    · rw [Pi.single_eq_of_ne h1.symm, eq_comm, max_eq_left_iff, sub_nonpos]
      refine Int.add_one_le_of_lt (a := 0) (Int.natAbs_sq _ ▸ pow_pos ?_ 2)
      rw [Int.natCast_natAbs, abs_pos, sub_ne_zero, ne_eq, Int.ofNat_inj, Fin.val_inj]
      exact h1.symm
  exact AddMaxClosed.eq_univ_of_neg_one_and_single_mem hS0 h0 h hS





/-! ### Minimal size of add-sup generator -/

def good (ι : Type*) (n : ℕ) := ∃ I : Finset (ι → ℤ), I.card ≤ n ∧ AddSupGenerator I


namespace good

theorem of_Nat_le (h : n ≤ k) : good ι n → good ι k :=
  λ ⟨I, hI, hI0⟩ ↦ ⟨I, hI.trans h, hI0⟩

theorem iff_of_self_and_succ (hN : ¬good ι N) (hN0 : good ι N.succ) :
    good ι n ↔ N.succ ≤ n :=
  ⟨λ h ↦ Nat.lt_of_not_le λ h0 ↦ hN (h.of_Nat_le h0), hN0.of_Nat_le⟩


variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem of_Fintype_card_le (h : Fintype.card β ≤ Fintype.card α) : good α n → good β n := by
  rintro ⟨A, hA, hA0⟩
  obtain ⟨ι⟩ : Nonempty (β ↪ α) := Function.Embedding.nonempty_of_card_le h
  exact ⟨A.image (· ∘ ι), Finset.card_image_le.trans hA, hA0.ofEmbedding ι⟩

theorem iff_Fintype_card_eq (h : Fintype.card α = Fintype.card β) : good α n ↔ good β n :=
  ⟨λ hn ↦ hn.of_Fintype_card_le h.symm.le, λ hn ↦ hn.of_Fintype_card_le h.le⟩

end good



/-! ##### `good` on explicit types -/

theorem good_Empty_iff : good Empty n ↔ 1 ≤ n := by
  refine good.iff_of_self_and_succ ?_ ?_
  · rintro ⟨I, hI, hI0⟩
    rw [Nat.le_zero, Finset.card_eq_zero] at hI
    subst hI; exact empty_not_AddSupGenerator hI0
  · refine ⟨{0}, Nat.le_refl 1, ?_⟩
    rw [Finset.singleton_eq_univ]; exact AddSupGenerator.univ

theorem not_good_one_of_Nonempty [hι : Nonempty ι] : ¬good ι 1 := by
  rintro ⟨I, hI, hI0⟩
  rw [Nat.le_one_iff_eq_zero_or_eq_one, Finset.card_eq_zero, Finset.card_eq_one] at hI
  rcases hI with rfl | ⟨v, rfl⟩
  exacts [empty_not_AddSupGenerator hI0, singleton_not_AddSupGenerator v hI0]

theorem good_Fin2_two : good (Fin 2) 2 :=
  ⟨_, Finset.card_le_two, Fin2_AddSupGenerator⟩

theorem not_good_Fin3_two : ¬good (Fin 3) 2 := by
  rintro ⟨I, hI, hI0⟩
  rw [Nat.le_succ_iff, Finset.card_eq_two] at hI
  rcases hI with hI | ⟨x, y, -, rfl⟩
  exacts [not_good_one_of_Nonempty ⟨I, hI, hI0⟩, Fin3_doubleton_not_AddSupGenerator _ _ hI0]

theorem good_Fin_three (n : ℕ) : good (Fin n.succ) 3 :=
  ⟨_, Finset.card_le_three, Fin_general_AddSupGenerator n⟩





/-! ### Summary -/

variable [Fintype ι] [DecidableEq ι]

theorem good_Fintype_iff₁ (hι : Fintype.card ι = 0) : good ι n ↔ 1 ≤ n := by
  rw [good.iff_Fintype_card_eq (β := Empty) hι, good_Empty_iff]

theorem good_Fintype_iff₂ (hι : Fintype.card ι ≠ 0) (hι0 : Fintype.card ι ≤ 2) :
    good ι n ↔ 2 ≤ n :=
  have : Nonempty ι := (isEmpty_or_nonempty ι).resolve_left λ _ ↦ hι Fintype.card_eq_zero
  good.iff_of_self_and_succ not_good_one_of_Nonempty
    (good_Fin2_two.of_Fintype_card_le (α := Fin 2) hι0)

theorem good_Fintype_iff₃ (hι : 3 ≤ Fintype.card ι) : good ι n ↔ 3 ≤ n :=
  good.iff_of_self_and_succ
    (λ h ↦ not_good_Fin3_two (h.of_Fintype_card_le hι))
    ((good_Fin_three (Fintype.card ι)).of_Fintype_card_le <|
      (Nat.le_succ _).trans_eq (Fintype.card_fin _).symm)

/-- Final solution -/
theorem final_solution :
    good ι n ↔ n ≥ if Fintype.card ι = 0 then 1 else
      if Fintype.card ι ≤ 2 then 2 else 3 := by
  split_ifs with h h0
  exacts [good_Fintype_iff₁ h, good_Fintype_iff₂ h h0,
    good_Fintype_iff₃ (Nat.lt_of_not_le h0)]
