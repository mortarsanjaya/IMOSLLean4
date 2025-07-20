/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# IMO 2018 C1

Let $n ≥ 4$ be an integer and $S ⊆ ℕ^+$.
We say that $S$ is *good* if for each $m ∈ ℕ$ with $2 ≤ m ≤ n - 2$, there exists
  $T ⊆ S$ of size $m$ such that the sum of all elements in $T$ and $S \ T$ are equal.
Prove that for any $n ≥ 4$, there exists a good set of size $n$.
-/

namespace IMOSL
namespace IMO2018C1

open Finset

/-! ### Definitions -/

def good (S : Finset ℕ) :=
  ∀ m ≥ 2, m + 2 ≤ S.card → ∃ T ⊆ S, T.card = m ∧ T.sum id = (S \ T).sum id

lemma good_iff {S : Finset ℕ} :
    good S ↔ ∀ m ≥ 2, m ≤ S.card / 2 → ∃ T ⊆ S, T.card = m ∧ 2 * T.sum id = S.sum id := by
  have X {T} (h : T ⊆ S) : T.sum id = (S \ T).sum id ↔ 2 * T.sum id = S.sum id := by
    rw [← Nat.add_left_inj, ← Nat.two_mul, sum_sdiff h]
  refine ⟨λ hS m hm hm0 ↦ ?_, λ hS m hm hm0 ↦ ?_⟩
  ---- `→` direction
  · replace hm0 : m + 2 ≤ S.card := calc
      _ ≤ m + m := Nat.add_le_add_left hm m
      _ = m * 2 := m.mul_two.symm
      _ ≤ S.card := Nat.mul_le_of_le_div _ _ _ hm0
    obtain ⟨T, hT, hT0, hT1⟩ := hS m hm hm0
    exact ⟨T, hT, hT0, (X hT).mp hT1⟩
  ---- `←` direction
  · obtain hm1 | hm1 : m ≤ S.card / 2 ∨ S.card / 2 < m := le_or_gt _ _
    · obtain ⟨T, hT, hT0, hT1⟩ := hS m hm hm1
      exact ⟨T, hT, hT0, (X hT).mpr hT1⟩
    · replace hm : m ≤ S.card := Nat.le_of_add_right_le hm0
      replace hm0 : 2 ≤ S.card - m := Nat.le_sub_of_add_le' hm0
      replace hm1 : S.card - m ≤ S.card / 2 := Nat.sub_le_of_le_add <| calc
        _ = 2 * (S.card / 2) + S.card % 2 := (Nat.div_add_mod _ _).symm
        _ ≤ 2 * (S.card / 2) + 1 :=
          Nat.add_le_add_left (Nat.le_of_lt_succ (Nat.mod_lt _ Nat.two_pos)) _
        _ = S.card / 2 + (S.card / 2 + 1) := by rw [Nat.two_mul, Nat.add_assoc]
        _ ≤ S.card / 2 + m := Nat.add_le_add_left hm1 _
      obtain ⟨T, hT, hT0, hT1⟩ := hS (S.card - m) hm0 hm1
      refine ⟨S \ T, sdiff_subset, ?_, ?_⟩
      · rw [card_sdiff hT, hT0, Nat.sub_sub_self hm]
      · rwa [sdiff_sdiff_right_self, inf_eq_inter, inter_eq_right.mpr hT, eq_comm, X hT]

theorem good_of_card_lt_four {S : Finset ℕ} (hS : S.card < 4) : good S :=
  λ _ hm hm0 ↦ absurd hm0 (Nat.not_le_of_lt (hS.trans_le (Nat.add_le_add_right hm 2)))





/-! ### "Base" good set, defined for convenience -/

def GoodSetBase (N : ℕ) : Finset ℕ :=
  ((range N).image (2 * 3 ^ ·)) ∪ ((range N).image (4 * 3 ^ ·))

lemma mul_three_pow_inj (n : ℕ) : (n.succ * 3 ^ ·).Injective :=
  λ _ _ h ↦ Nat.pow_right_injective (by decide : 1 < 3) (Nat.mul_left_cancel n.succ_pos h)

lemma image_mul_three_pow_disj (N) :
    Disjoint ((range N).image (2 * 3 ^ ·)) ((range N).image (4 * 3 ^ ·)) := by
  refine disjoint_iff_ne.mpr λ a ha b hb h ↦ ?_
  rw [mem_image] at ha hb
  rcases ha with ⟨k, -, rfl⟩
  rcases hb with ⟨m, -, rfl⟩
  rw [Nat.mul_assoc 2 2, Nat.mul_right_inj (Nat.succ_ne_zero 1)] at h
  apply absurd (congrArg (· % 2) h : _ % 2 = _ % 2)
  rw [Nat.mul_mod_right, Nat.pow_mod, Nat.one_pow]
  exact Nat.one_ne_zero

lemma GoodSetBase_card (N : ℕ) : (GoodSetBase N).card = 2 * N := calc
  _ = ((range N).image (2 * 3 ^ ·)).card + ((range N).image (4 * 3 ^ ·)).card :=
    card_union_of_disjoint (image_mul_three_pow_disj N)
  _ = (range N).card + (range N).card :=
    let X (n) := card_image_of_injective (range N) (mul_three_pow_inj n)
    congrArg₂ _ (X _) (X _)
  _ = _ := by rw [card_range, Nat.two_mul]

lemma GoodSetBase_pos (hx : x ∈ GoodSetBase N) : 0 < x := by
  rw [GoodSetBase, mem_union, mem_image, mem_image] at hx
  rcases hx with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩
  all_goals exact Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (Nat.succ_pos 2))

lemma GoodSetBase_sum (N : ℕ) : (GoodSetBase N).sum id + 3 = 3 ^ (N + 1) := by
  have X (n : ℕ) :
      ((range N).image (n.succ * 3 ^ ·)).sum id = ∑ k ∈ range N, n.succ * 3 ^ k :=
    sum_image λ _ _ _ _ h ↦ mul_three_pow_inj n h
  rw [GoodSetBase, sum_union (image_mul_three_pow_disj N), X, X]
  clear X; induction' N with N hN; rfl
  rw [sum_range_succ, sum_range_succ, add_add_add_comm, add_right_comm, hN, ← Nat.add_mul,
    Nat.mul_assoc 2 3, ← Nat.pow_succ', add_comm, ← Nat.succ_mul, ← Nat.pow_succ']

lemma GoodSetBase_two_dvd_of_mem (hx : x ∈ GoodSetBase N) : 2 ∣ x := by
  rw [GoodSetBase, mem_union, mem_image, mem_image] at hx
  rcases hx with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩
  exacts [Nat.dvd_mul_right 2 _, ⟨2 * 3 ^ k, Nat.mul_assoc 2 2 _⟩]





/-! ### Desired subsets of a good base set -/

def GoodSubsetBase (K m : ℕ) : Finset ℕ :=
  insert (2 * 3 ^ K) ((range m).image λ k ↦ 4 * 3 ^ (K + k))

lemma GoodSubsetBase_subset_GoodSetBase (hm : 0 < m) (h : K + m ≤ N) :
    GoodSubsetBase K m ⊆ GoodSetBase N := by
  show ∀ x ∈ insert (2 * 3 ^ K) _, x ∈ GoodSetBase N
  refine (forall_mem_insert _ _ _).mpr ⟨?_, forall_mem_image.mpr λ k hk ↦ ?_⟩
  · refine mem_union_left _ (mem_image.mpr ⟨K, ?_, rfl⟩)
    exact mem_range.mpr ((Nat.lt_add_of_pos_right hm).trans_le h)
  · refine mem_union_right _ (mem_image.mpr ⟨K + k, mem_range.mpr ?_, rfl⟩)
    exact (Nat.add_lt_add_left (mem_range.mp hk) _).trans_le h

lemma GoodSubsetBase_disjoint' (K m : ℕ) :
    2 * 3 ^ K ∉ (range m).image λ k ↦ 4 * 3 ^ (K + k) := by
  rw [mem_image]; rintro ⟨k, -, h⟩
  rw [Nat.mul_assoc 2 2, Nat.mul_right_inj (Nat.succ_ne_zero 1)] at h
  apply absurd (congrArg (· % 2) h : _ % 2 = _ % 2)
  rw [Nat.mul_mod_right, Nat.pow_mod, Nat.one_pow]
  exact Nat.zero_ne_one

lemma mul_three_pow_add_inj (n K : ℕ) : (λ k ↦ n.succ * 3 ^ (K + k)).Injective :=
  λ _ _ h ↦ Nat.add_left_cancel (mul_three_pow_inj n h)

lemma GoodSubsetBase_card (K m) : (GoodSubsetBase K m).card = m + 1 := by
  rw [GoodSubsetBase, card_insert_of_notMem (GoodSubsetBase_disjoint' K m),
    card_image_of_injective _ (mul_three_pow_add_inj 3 _), card_range]

lemma GoodSubsetBase_sum (K m) : (GoodSubsetBase K m).sum id = 2 * 3 ^ (K + m) := by
  rw [GoodSubsetBase, sum_insert (GoodSubsetBase_disjoint' K m),
    sum_image λ _ _ _ _ h ↦ mul_three_pow_add_inj 3 _ h]
  induction' m with m m_ih; rfl
  rw [sum_range_succ, ← Nat.add_assoc, m_ih, ← Nat.add_assoc, Nat.pow_succ,
    ← Nat.mul_assoc, Nat.mul_succ, Nat.mul_right_comm, Nat.add_comm]; rfl





/-! ### Even case -/

def EvenGoodSet (N : ℕ) : Finset ℕ := GoodSetBase N ∪ {1, 3 ^ N + 2}

theorem EvenGoodSet_disjoint (N : ℕ) : Disjoint (GoodSetBase N) {1, 3 ^ N + 2} := by
  refine disjoint_iff_ne.mpr λ a ha b hb h ↦ ?_
  replace ha : a % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (GoodSetBase_two_dvd_of_mem ha)
  rw [mem_insert, mem_singleton] at hb
  subst b; rcases hb with rfl | rfl
  · exact absurd ha Nat.one_ne_zero
  · rw [Nat.add_mod_right, Nat.pow_mod, Nat.one_pow] at ha
    exact absurd ha Nat.one_ne_zero

theorem EvenGoodSet_card (N : ℕ) : (EvenGoodSet N).card = 2 * (N + 1) := by
  rw [EvenGoodSet, card_union_of_disjoint (EvenGoodSet_disjoint N)]
  exact congrArg₂ _ (GoodSetBase_card N) rfl

theorem EvenGoodSet_pos (hx : x ∈ EvenGoodSet N) : 0 < x := by
  rw [EvenGoodSet, mem_union, mem_insert, mem_singleton] at hx
  rcases hx with hx | rfl | rfl
  exacts [GoodSetBase_pos hx, Nat.one_pos, Nat.succ_pos _]

theorem EvenGoodSet_sum (N : ℕ) : (EvenGoodSet N).sum id = 4 * 3 ^ N := calc
  _ = (GoodSetBase N).sum id + (1 + (3 ^ N + 2)) := sum_union (EvenGoodSet_disjoint N)
  _ = _ := by rw [Nat.add_left_comm 1, Nat.add_left_comm, GoodSetBase_sum,
    Nat.pow_succ, Nat.add_comm, ← Nat.mul_succ, Nat.mul_comm]

theorem EvenGoodSet_good (N : ℕ) : good (EvenGoodSet N) := by
  refine good_iff.mpr λ m hm hm0 ↦ ?_
  rw [EvenGoodSet_card, Nat.mul_div_cancel_left _ Nat.two_pos] at hm0
  replace hm0 : m - 1 ≤ N := Nat.pred_le_pred hm0
  refine ⟨GoodSubsetBase (N - (m - 1)) (m - 1), ?_, ?_, ?_⟩
  · exact (GoodSubsetBase_subset_GoodSetBase (Nat.pred_le_pred hm)
      (Nat.sub_add_cancel hm0).le).trans subset_union_left
  · rw [GoodSubsetBase_card, Nat.sub_add_cancel (Nat.one_le_of_lt hm)]
  · rw [GoodSubsetBase_sum, Nat.sub_add_cancel hm0, EvenGoodSet_sum, ← Nat.mul_assoc]





/-! ### Odd case -/

def OddGoodSet (N : ℕ) : Finset ℕ := insert (3 ^ N + 3) (GoodSetBase N)

theorem OddGoodSet_disjoint (hN : 2 < N) : 3 ^ N + 3 ∉ GoodSetBase N := by
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := Nat.exists_eq_add_of_le' (Nat.zero_lt_of_lt hN)
  rw [GoodSetBase, mem_union, mem_image, mem_image]
  have X : 0 < 3 := Nat.succ_pos 2
  rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩)
  ---- Case 1: `3^N + 3 = 2 * 3^k` (with `k ≤ N`)
  · apply h.not_lt; calc
      _ < 3 * 3 ^ N := Nat.mul_lt_mul_of_lt_of_le (Nat.lt_succ_self 2)
        (Nat.pow_le_pow_right X (Nat.le_of_lt_succ (mem_range.mp hk))) (Nat.pow_pos X)
      _ = 3 ^ (N + 1) := Nat.pow_succ'.symm
      _ ≤ 3 ^ (N + 1) + 3 := Nat.le_add_right _ _
  ---- Case 2: `3^N + 3 = 4 * 3^k` (with `k ≤ N`)
  · rw [mem_range, Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hk
    rcases hk with hk | rfl
    -- Subcase 2.1: `k < N`
    · apply h.not_lt; calc
      _ < 9 * 3 ^ k := Nat.mul_lt_mul_of_lt_of_le (by decide)
        (Nat.pow_le_pow_right X k.le_refl) (Nat.pow_pos X)
      _ = 3 ^ (k + 2) := by rw [← Nat.pow_add 3 2, Nat.add_comm]
      _ ≤ 3 ^ (N + 1) := Nat.pow_le_pow_right X (Nat.succ_le_succ hk)
      _ ≤ 3 ^ (N + 1) + 3 := Nat.le_add_right _ _
    -- Subcase 2.2: `k = N`
    · rw [Nat.succ_mul, Nat.pow_succ', Nat.add_right_inj] at h
      exact h.not_gt (Nat.pow_lt_pow_right (by decide : 1 < 3) (Nat.lt_of_succ_lt_succ hN))

theorem OddGoodSet_card (hN : 2 < N) : (OddGoodSet N).card = 2 * N + 1 := by
  rw [OddGoodSet, card_insert_of_notMem (OddGoodSet_disjoint hN)]
  exact congrArg₂ _ (GoodSetBase_card N) rfl

theorem OddGoodSet_pos (hx : x ∈ OddGoodSet N) : 0 < x := by
  rw [OddGoodSet, mem_insert] at hx
  rcases hx with rfl | hx
  exacts [Nat.succ_pos _, GoodSetBase_pos hx]

theorem OddGoodSet_sum (hN : 2 < N) : (OddGoodSet N).sum id = 4 * 3 ^ N := calc
  _ =  (3 ^ N + 3) + (GoodSetBase N).sum id := sum_insert (OddGoodSet_disjoint hN)
  _ = _ := by rw [← add_rotate, Nat.add_right_comm,
    GoodSetBase_sum, Nat.pow_succ', ← Nat.succ_mul]

theorem OddGoodSet_good (hN : 2 < N) : good (OddGoodSet N) := by
  refine good_iff.mpr λ m hm hm0 ↦ ?_
  rw [OddGoodSet_card hN, Nat.mul_add_div Nat.two_pos] at hm0
  replace hm0 : m - 1 ≤ N := m.pred_le.trans hm0
  refine ⟨GoodSubsetBase (N - (m - 1)) (m - 1), ?_, ?_, ?_⟩
  · refine (GoodSubsetBase_subset_GoodSetBase (Nat.pred_le_pred hm)
      (Nat.sub_add_cancel hm0).le).trans (subset_insert _ _)
  · rw [GoodSubsetBase_card, Nat.sub_add_cancel (Nat.one_le_of_lt hm)]
  · rw [GoodSubsetBase_sum, Nat.sub_add_cancel hm0, OddGoodSet_sum hN, ← Nat.mul_assoc]





/-! ### Final solution -/

/-- Final solution -/
theorem final_solution (n : ℕ) : ∃ S : Finset ℕ, S.card = n ∧ (∀ x ∈ S, 0 < x) ∧ good S := by
  ---- First eliminate the case `n < 4`
  obtain hn | hn : n / 2 < 2 ∨ 2 ≤ n / 2 := lt_or_ge _ _
  · have h : ((range n).image Nat.succ).card = n := by
      rw [card_image_of_injective _ Nat.succ_injective, card_range]
    exact ⟨(range n).image Nat.succ, h, forall_mem_image.mpr λ k _ ↦ k.succ_pos,
      good_of_card_lt_four (h.trans_lt (Nat.lt_mul_of_div_lt hn Nat.two_pos))⟩
  ---- Write `n = 2(q + 2) + r` where `r < 2`
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ n = 2 * (q + 2) + r := by
    refine ⟨n / 2 - 2, n % 2, Nat.mod_lt n Nat.two_pos, ?_⟩
    rw [Nat.sub_add_cancel hn, Nat.div_add_mod]
  ---- Divide case on `r`, with the case `r = 0` (`n` even) immediate
  clear hn; rw [Nat.lt_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one] at hr
  rcases hr with rfl | rfl
  · exact ⟨EvenGoodSet _, EvenGoodSet_card _, λ _ ↦ EvenGoodSet_pos, EvenGoodSet_good _⟩
  ---- Now assume that `r = 1`, and resolve the case `q > 0`
  obtain hq | rfl : 0 < q ∨ q = 0 := q.eq_zero_or_pos.symm
  · have hq0 : 2 < q + 2 := Nat.lt_add_of_pos_left hq
    exact ⟨OddGoodSet _, OddGoodSet_card hq0, λ _ ↦ OddGoodSet_pos, OddGoodSet_good hq0⟩
  ---- Finally, solve the problem for `n = 5`
  refine ⟨{4, 5, 6, 7, 8}, rfl, by decide, good_iff.mpr λ m hm hm0 ↦ ?_⟩
  exact ⟨{7, 8}, by decide, hm.antisymm hm0, rfl⟩
