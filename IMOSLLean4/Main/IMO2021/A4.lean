/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen

/-!
# IMO 2021 A4 (P2)

Prove that for any real numbers $x_1, x_2, …, x_n$,
$$ \sum_{i = 1}^n \sum_{j = 1}^n \sqrt{|x_i - x_j|}
  ≤ \sum_{i = 1}^n \sum_{j = 1}^n \sqrt{|x_i + x_j|}. $$

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2021SL.pdf).
More generally, we prove that for any increasing and concave function $g : ℝ_{≥ 0} → ℝ$,
$$ \sum_{i = 1}^n \sum_{j = 1}^n g(|x_i - x_j|)
  ≤ \sum_{i = 1}^n \sum_{j = 1}^n g(|x_i + x_j|). $$
Instead of taking $T$ large enough, we split into three cases:
1. $x_i ≥ 0$ for all $i$;
2. $x_i ≤ 0$ for all $i$;
3. some of the $x_i$'s are positive while some others are negative.
-/

namespace IMOSL
namespace IMO2021A4

/-! ### Subset relations of intervals -/

/-- If `c ≤ a`, then `[a, b] ⊆ [c, ∞)`. -/
theorem Icc_subset_Ici [Preorder α] {a b c : α} (h : c ≤ a) :
    Set.Icc a b ⊆ Set.Ici c :=
  λ _ hd ↦ Set.mem_Ici.mpr (h.trans (Set.mem_Icc.mp hd).1)

/-- If `b ≤ c`, then `[a, b] ⊆ (-∞, c]`. -/
theorem Icc_subset_Iic [Preorder α] {a b c : α} (h : b ≤ c) :
    Set.Icc a b ⊆ Set.Iic c :=
  λ _ hd ↦ Set.mem_Iic.mpr ((Set.mem_Icc.mp hd).2.trans h)





/-! ### Some concavity properties -/

section

open Set

variable [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [LinearOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E]
  [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β] (g : E → β) (hg : ConcaveOn 𝕜 (Ici 0) g)
include g hg

/-- If `g` is concave on non-negative inputs, then `t ↦ g(|t|)` is concave on `[0, ∞)`. -/
theorem ConcaveOn_abs_zero_Ici : ConcaveOn 𝕜 (Ici 0) (λ t ↦ g |t|) :=
  hg.congr λ _ hx ↦ congrArg g (abs_of_nonneg (mem_Ici.mp hx)).symm

/-- If `g` is concave on non-negative inputs, then `t ↦ g(|t|)` is concave on `(-∞, 0]`. -/
theorem ConcaveOn_abs_zero_Iic : ConcaveOn 𝕜 (Iic 0) (λ t ↦ g |t|) := by
  have h : (-LinearMap.id (R := 𝕜) (M := E)) ⁻¹' Ici 0 = Iic 0 := by
    ext x; change -x ∈ Ici 0 ↔ x ∈ Iic 0
    rw [mem_Ici, mem_Iic, neg_nonneg]
  replace h : ConcaveOn 𝕜 (Iic 0) (λ t ↦ g |-t|) :=
    h ▸ (ConcaveOn_abs_zero_Ici g hg).comp_linearMap (-LinearMap.id)
  simpa only [abs_neg] using h

/-- If `g` is concave on non-negative inputs, then for any `x ∈ E`,
  the function `t ↦ g(|x - t|)` is concave on `(-∞, x]`. -/
theorem ConcaveOn_abs_sub_Ici (x) : ConcaveOn 𝕜 (Iic x) (λ t ↦ g |x - t|) := by
  have h : (-x + ·) ⁻¹' Iic 0 = Iic x :=
    ext λ x ↦ by rw [preimage_const_add_Iic, sub_neg_eq_add, zero_add, mem_Iic]
  conv => right; ext t; rw [abs_sub_comm, sub_eq_add_neg]
  exact h ▸ (ConcaveOn_abs_zero_Iic g hg).translate_left (-x)

/-- If `g` is concave on non-negative inputs, then for any `x ∈ E`,
  the function `t ↦ g(|x - t|)` is concave on `[x, ∞)`. -/
theorem ConcaveOn_abs_sub_Iic (x) : ConcaveOn 𝕜 (Ici x) (λ t ↦ g |x - t|) := by
  have h : (-x + ·) ⁻¹' Ici 0 = Ici x :=
    ext λ x ↦ by rw [preimage_const_add_Ici, sub_neg_eq_add, zero_add, mem_Ici]
  conv => right; ext t; rw [abs_sub_comm, sub_eq_add_neg]
  exact h ▸ (ConcaveOn_abs_zero_Ici g hg).translate_left (-x)

end


section

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
  [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β]
  [DecidableEq ι] (S : Finset ι) {s : Set E} (hs : Convex 𝕜 s)
  (g : ι → E → β) (hg : ∀ i ∈ S, ConcaveOn 𝕜 s (g i))
include hs hg

/-- The sum of concave functions on a subset is concave on the same subset.
  This should eventually get into `mathlib`. -/
theorem ConcaveOn_sum : ConcaveOn 𝕜 s (∑ i ∈ S, g i) := by
  induction S using Finset.induction_on with
  | empty => exact concaveOn_const 0 hs
  | insert i S hiS h =>
      rw [Finset.forall_mem_insert] at hg
      rw [Finset.sum_insert hiS]
      exact hg.1.add (h hg.2)

/-- The sum of concave functions on a subset is concave on the same subset.
  This should eventually get into `mathlib`. -/
theorem ConcaveOn_of_sum_eq {f : E → β} (hf : ∀ x, f x = ∑ i ∈ S, g i x) :
    ConcaveOn 𝕜 s f := by
  obtain rfl : f = ∑ i ∈ S, g i := funext λ x ↦ (hf x).trans (Finset.sum_apply _ _ _).symm
  exact ConcaveOn_sum S hs g hg

end


/-- If a function is concave on a closed interval, then the function attains its minimum
  on the interval at one of the endpoints. This should eventually get into `mathlib`. -/
theorem ConcaveOn_min_endpoints_le [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β]
    [IsStrictOrderedModule 𝕜 β] {f : 𝕜 → β} (hf : ConcaveOn 𝕜 (Set.Icc x y) f)
    (hxz : x ≤ z) (hzy : z ≤ y) : min (f x) (f y) ≤ f z := by
  have h : x ≤ y := hxz.trans hzy
  exact hf.min_le_of_mem_Icc (Set.left_mem_Icc.mpr h)
    (Set.right_mem_Icc.mpr h) (Set.mem_Icc.mpr ⟨hxz, hzy⟩)





/-! ### Start of the problem -/

open Finset

section

variable [AddCommGroup 𝕜] [LinearOrder 𝕜] [AddCommGroup β] (g : 𝕜 → β)

/-- The "target sum": `∑_{i, j ∈ S} (g(|x_i + x_j|) - g(|x_i - x_j|))`. -/
def targetSum (S : Finset ι) (x : ι → 𝕜) : β :=
  ∑ p ∈ S ×ˢ S, (g |x p.1 + x p.2| - g |x p.1 - x p.2|)

/-- If `x_i = 0`, then the value of the target sum with
  index set `S ∪ {i}` and index set `S` are equal. -/
theorem targetSum_insert_of_eq_zero
    [DecidableEq ι] (S : Finset ι) (x : ι → 𝕜) (hi : x i = 0) :
    targetSum g (insert i S) x = targetSum g S x := by
  obtain h | h : i ∈ S ∨ ¬i ∈ S := dec_em _
  ---- Case 1: `i ∈ S`.
  · rw [insert_eq_of_mem h]
  ---- Case 2: `i ∉ S`.
  · calc ∑ p ∈ insert i S ×ˢ insert i S, (g |x p.1 + x p.2| - g |x p.1 - x p.2|)
      _ = ∑ j ∈ insert i S, (g |x i + x j| - g |x i - x j|)
          + ∑ j₁ ∈ S, ∑ j₂ ∈ insert i S, (g |x j₁ + x j₂| - g |x j₁ - x j₂|) := by
        rw [sum_product, sum_insert h]
      _ = ∑ j₁ ∈ S, ∑ j₂ ∈ insert i S, (g |x j₁ + x j₂| - g |x j₁ - x j₂|) := by
        refine add_eq_right.mpr (sum_eq_zero λ j _ ↦ ?_)
        rw [hi, zero_add, zero_sub, abs_neg, sub_self]
      _ = ∑ j₁ ∈ S, ∑ j₂ ∈ S, (g |x j₁ + x j₂| - g |x j₁ - x j₂|) := by
        refine sum_congr rfl λ j₁ _ ↦ ?_
        rw [sum_insert h, add_eq_right, hi, add_zero, sub_zero, sub_self]
      _ = ∑ p ∈ S ×ˢ S, (g |x p.1 + x p.2| - g |x p.1 - x p.2|) := by
        rw [sum_product]

/-- If `i₁ ≠ i₂ ∉ S` and `x_{i₁} + x_{i₂} = 0`, then the value of the target sum with
  index set `S ∪ {i, j}` and index set `S` are equal. -/
theorem targetSum_insert_of_add_eq_zero [DecidableEq ι] (S : Finset ι)
    (hi : Disjoint {i₁, i₂} S) (hi0 : i₁ ≠ i₂) (x : ι → 𝕜) (hi1 : x i₁ + x i₂ = 0) :
    targetSum g ({i₁, i₂} ∪ S) x = targetSum g S x :=
  have hi1 : x i₂ = -x i₁ := eq_neg_of_add_eq_zero_right hi1
  calc ∑ p ∈ ({i₁, i₂} ∪ S) ×ˢ ({i₁, i₂} ∪ S), (g |x p.1 + x p.2| - g |x p.1 - x p.2|)
  _ = ∑ j₁ ∈ {i₁, i₂}, ∑ j₂ ∈ {i₁, i₂} ∪ S, (g |x j₁ + x j₂| - g |x j₁ - x j₂|)
      + ∑ j₁ ∈ S, ∑ j₂ ∈ {i₁, i₂} ∪ S, (g |x j₁ + x j₂| - g |x j₁ - x j₂|) := by
    rw [sum_product, sum_union hi]
  _ = ∑ j₁ ∈ S, ∑ j₂ ∈ {i₁, i₂} ∪ S, (g |x j₁ + x j₂| - g |x j₁ - x j₂|) := by
    rw [add_eq_right, sum_pair hi0, ← sum_add_distrib]
    refine sum_eq_zero λ j _ ↦ ?_
    rw [hi1, ← neg_add', abs_neg, sub_add_sub_cancel',
      neg_add_eq_sub, abs_sub_comm, sub_self]
  _ = ∑ j₁ ∈ S, ∑ j₂ ∈ S, (g |x j₁ + x j₂| - g |x j₁ - x j₂|) := by
    refine sum_congr rfl λ j₁ _ ↦ ?_
    rw [sum_union hi, add_eq_right, sum_pair hi0, hi1, sub_neg_eq_add,
      sub_add_sub_cancel', ← sub_eq_add_neg, abs_sub_comm, sub_self]
  _ = ∑ p ∈ S ×ˢ S, (g |x p.1 + x p.2| - g |x p.1 - x p.2|) := by
    rw [sum_product]

end


section

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup β]
  [LinearOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]
  (g : 𝕜 → β) (hg : ∀ y ≥ 0, ∀ x ≥ y, g x ≥ g y) (hg0 : ConcaveOn 𝕜 (Set.Ici 0) g)
include hg hg0

/-- If `S` is non-empty, then there exists a pair `(i₁, i₂) ∈ S^2` such that the target sum
  with `x_i - (x_{i_1} + x_{i_2})/2` is less than or equal to the target sum with `x_i`. -/
theorem exists_targetSum_shift_le_targetSum
    [DecidableEq ι] {S : Finset ι} (hS : S.Nonempty) (x : ι → 𝕜) :
    ∃ p ∈ S ×ˢ S, targetSum g S (λ i ↦ x i - (x p.1 + x p.2) / 2) ≤ targetSum g S x := by
  ---- If `x_i ≥ 0` for all `i ∈ S`, then take `p = (i, i)` where `x_i` is minimal.
  by_cases hS_pos : ∀ i ∈ S, x i ≥ 0
  · obtain ⟨i, hiS, hi⟩ : ∃ i ∈ S, ∀ j ∈ S, x i ≤ x j := S.exists_min_image _ hS
    refine ⟨(i, i), mk_mem_product hiS hiS, sum_le_sum λ p hp ↦ ?_⟩
    replace hi (j) (hj : j ∈ S) : 0 ≤ x j - x i := sub_nonneg.mpr (hi j hj)
    replace hp : p.1 ∈ S ∧ p.2 ∈ S := mem_product.mp hp
    rw [add_self_div_two, sub_sub_sub_cancel_right, sub_le_sub_iff_right]
    refine hg _ (abs_nonneg _) _ ?_
    calc |x p.1 + x p.2|
      _ = x p.1 + x p.2 := abs_of_nonneg (add_nonneg (hS_pos _ hp.1) (hS_pos _ hp.2))
      _ ≥ (x p.1 - x i) + (x p.2 - x i) := by
        have hi0 : 0 ≤ x i := hS_pos i hiS
        exact add_le_add (sub_le_self _ hi0) (sub_le_self _ hi0)
      _ = |(x p.1 - x i) + (x p.2 - x i)| :=
        (abs_of_nonneg (add_nonneg (hi _ hp.1) (hi _ hp.2))).symm
  ---- If `x_i ≤ 0` for all `i ∈ S`, then take `p = (i, i)` where `x_i` is maximal.
  by_cases hS_neg : ∀ i ∈ S, x i ≤ 0
  · obtain ⟨i, hiS, hi⟩ : ∃ i ∈ S, ∀ j ∈ S, x j ≤ x i := S.exists_max_image _ hS
    refine ⟨(i, i), mk_mem_product hiS hiS, sum_le_sum λ p hp ↦ ?_⟩
    replace hi (j) (hj : j ∈ S) : x j - x i ≤ 0 := sub_nonpos.mpr (hi j hj)
    replace hp : p.1 ∈ S ∧ p.2 ∈ S := mem_product.mp hp
    rw [add_self_div_two, sub_sub_sub_cancel_right, sub_le_sub_iff_right]
    refine hg _ (abs_nonneg _) _ ?_
    calc |x p.1 + x p.2|
      _ = -(x p.1 + x p.2) := abs_of_nonpos (add_nonpos (hS_neg _ hp.1) (hS_neg _ hp.2))
      _ ≥ -((x p.1 - x i) + (x p.2 - x i)) := by
        have hi0 : x i ≤ 0 := hS_neg i hiS
        refine neg_le_neg (add_le_add ?_ ?_)
        all_goals exact (le_sub_self_iff _).mpr hi0
      _ = |(x p.1 - x i) + (x p.2 - x i)| :=
        (abs_of_nonpos (add_nonpos (hi _ hp.1) (hi _ hp.2))).symm
  ---- In the remaining case, we know that `x_i + x_j` takes both signs over `i, j ∈ S`.
  simp_rw [not_forall, not_le] at hS_pos hS_neg
  replace hS_pos : {p ∈ S ×ˢ S | x p.1 + x p.2 ≤ 0}.Nonempty := by
    rcases hS_pos with ⟨i, hi, hi0⟩
    exact ⟨(i, i), mem_filter.mpr ⟨mk_mem_product hi hi, (add_neg hi0 hi0).le⟩⟩
  replace hS_neg : {p ∈ S ×ˢ S | x p.1 + x p.2 ≥ 0}.Nonempty := by
    rcases hS_neg with ⟨i, hi, hi0⟩
    exact ⟨(i, i), mem_filter.mpr ⟨mk_mem_product hi hi, (add_pos hi0 hi0).le⟩⟩
  ---- First pick `pₚ = (iₚ, jₚ)` with `x_{iₚ + x_{jₚ}` minimally non-negative.
  obtain ⟨pₚ, hpₚ, hpₚ0, hpₚ1⟩ :
      ∃ p ∈ S ×ˢ S, x p.1 + x p.2 ≥ 0 ∧
        ∀ q ∈ S ×ˢ S, x q.1 + x q.2 ≥ 0 → x p.1 + x p.2 ≤ x q.1 + x q.2 := by
    obtain ⟨p, hp, hp0⟩ := exists_min_image _ (λ p : ι × ι ↦ x p.1 + x p.2) hS_neg
    simp_rw [mem_filter, and_imp] at hp hp0
    exact ⟨p, hp.1, hp.2, hp0⟩
  clear hS_neg
  ---- Now pick `pₙ = (iₙ, jₙ)` with `x_{iₙ} + x_{jₙ}` maximally non-positive.
  obtain ⟨pₙ, hpₙ, hpₙ0, hpₙ1⟩ :
      ∃ p ∈ S ×ˢ S, x p.1 + x p.2 ≤ 0 ∧
        ∀ q ∈ S ×ˢ S, x q.1 + x q.2 ≤ 0 → x q.1 + x q.2 ≤ x p.1 + x p.2 := by
    obtain ⟨p, hp, hp0⟩ := exists_max_image _ (λ p : ι × ι ↦ x p.1 + x p.2) hS_pos
    simp_rw [mem_filter, and_imp] at hp hp0
    exact ⟨p, hp.1, hp.2, hp0⟩
  clear hS_pos
  /- Claim: the target sum with respect to `t ↦ x_i - t/2` is concave on
    the interval `I = [x_{iₙ} + x_{jₙ}, x_{iₚ} + x_{jₚ}]`. -/
  let I : Set 𝕜 := Set.Icc (x pₙ.1 + x pₙ.2) (x pₚ.1 + x pₚ.2)
  have hI : Convex 𝕜 I := convex_Icc _ _
  have h : ConcaveOn 𝕜 I (λ t ↦ targetSum g S (λ i ↦ x i - t / 2)) := by
    refine ConcaveOn_of_sum_eq (S ×ˢ S) hI
      (λ p t ↦ g |x p.1 + x p.2 - t| + -g |x p.1 - x p.2|) ?_ ?_
    -- Check that each term `g(|x_i + x_j - t|)` is concave on `I`.
    · intro p hp; apply ConcaveOn.add_const
      obtain h | h : x p.1 + x p.2 ≤ 0 ∨ x p.1 + x p.2 ≥ 0 := le_total _ _
      exacts [(ConcaveOn_abs_sub_Iic g hg0 _).subset (Icc_subset_Ici (hpₙ1 p hp h)) hI,
        (ConcaveOn_abs_sub_Ici g hg0 _).subset (Icc_subset_Iic (hpₚ1 p hp h)) hI]
    -- Check that the sum of the functions match.
    · intro t; refine sum_congr rfl λ p _ ↦ ?_
      rw [sub_sub_sub_cancel_right, sub_add_sub_comm, add_halves, sub_eq_add_neg]
  ---- Now `0` belongs to that interval, so we can apply minimality on the endpoint.
  replace h :
      min (targetSum g S (λ i ↦ x i - (x pₙ.1 + x pₙ.2) / 2))
        (targetSum g S (λ i ↦ x i - (x pₚ.1 + x pₚ.2) / 2))
        ≤ targetSum g S (λ i ↦ x i - 0 / 2) :=
    ConcaveOn_min_endpoints_le (𝕜 := 𝕜) (β := β) h hpₙ0 hpₚ0
  ---- Picking one of the endpoints, we are done.
  simp_rw [zero_div, sub_zero, inf_le_iff] at h
  rcases h with h | h
  exacts [⟨pₙ, hpₙ, h⟩, ⟨pₚ, hpₚ, h⟩]

/-- Final solution, more general version. -/
theorem final_solution_monotone_concave [DecidableEq ι] (S : Finset ι) (x : ι → 𝕜) :
    targetSum g S x ≥ 0 := by
  ---- Proceed by strong induction on `S`.
  induction S using Finset.strongInduction generalizing x with | H S S_ih => ?_
  ---- If `S = ∅`, we are done.
  obtain rfl | hS : S = ∅ ∨ S.Nonempty := S.eq_empty_or_nonempty
  · exact le_refl 0
  /- If `S ≠ ∅`, by `exists_targetSum_shift_le_targetSum`, we can find `(i₁, i₂) ∈ S^2`
    such that the target sum with respect to `x_i - (x_{i_1} + x_{i_2})/2` is less than
    those with respect to `x_i`. -/
  obtain ⟨⟨i₁, i₂⟩, hi, h⟩ :
      ∃ p ∈ S ×ˢ S, targetSum g S (λ i ↦ x i - (x p.1 + x p.2) / 2) ≤ targetSum g S x :=
    exists_targetSum_shift_le_targetSum _ hg hg0 hS _
  replace hi : i₁ ∈ S ∧ i₂ ∈ S := mem_product.mp hi
  replace hi : {i₁, i₂} ⊆ S := by
    intro j hj
    rw [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl
    exacts [hi.1, hi.2]
  ---- Now prove the inequality by applying induction hypothesis on `S \ {i₁, i₂}`.
  calc 0
    _ ≤ targetSum g (S \ {i₁, i₂}) (x · - (x i₁ + x i₂) / 2) :=
      S_ih _ (sdiff_ssubset hi ⟨i₁, mem_insert_self _ _⟩) _
    _ = targetSum g ({i₁, i₂} ∪ (S \ {i₁, i₂})) (x · - (x i₁ + x i₂) / 2) := by
      obtain rfl | h1 : i₁ = i₂ ∨ i₁ ≠ i₂ := dec_em _
      -- If `i₁ = i₂`, use `targetSum_insert_of_eq_zero`.
      · rw [pair_eq_singleton]
        refine (targetSum_insert_of_eq_zero _ _ _ ?_).symm
        rw [add_self_div_two, sub_self]
      -- If `i₁ ≠ i₂`, use `targetSum_insert_of_add_eq_zero`.
      · refine (targetSum_insert_of_add_eq_zero _ _ disjoint_sdiff h1 _ ?_).symm
        rw [sub_add_sub_comm, add_halves, sub_self]
    _ = targetSum g S (x · - (x i₁ + x i₂) / 2) := by
      rw [union_sdiff_self_eq_union, union_eq_right.mpr hi]
    _ ≤ targetSum g S x := h

end


/-- Final solution -/
theorem final_solution [DecidableEq ι] (S : Finset ι) (x : ι → ℝ) :
    targetSum Real.sqrt S x ≥ 0 :=
  final_solution_monotone_concave _ (λ _ _ _ ↦ Real.sqrt_le_sqrt)
    Real.strictConcaveOn_sqrt.concaveOn S x
