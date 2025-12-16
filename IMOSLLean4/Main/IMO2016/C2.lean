/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# IMO 2016 C2

Find all positive integers $n$ such that the positive divisors of $n$ can be put into
  the cells of a rectangular table under the following constraints:
* each cell contains a distinct divisor;
* the sums of all rows are equal; and
* the sums of all columns are equal.

### Answer

$n = 1$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2016SL.pdf).
A table satisfying the latter two conditions is called a *good table*
  if distinct cells of the table contain distinct positive integers.
Note that this definition does not refer to $n$ at all.
-/

namespace IMOSL
namespace IMO2016C2

open Finset

/-- A `k × m` table is called *good* if distinct cells contain distinct positive integers,
  the sums of any two rows are equal and the sums of any two columns are equal.
The definition does not force the table to be non-empty.
To force non-emptiness, use `r + 1` and `c + 1` in place of `r` and `c`. -/
@[ext] structure IsGoodTable {r c} (T : Fin r × Fin c → ℕ) : Prop where
  injective : T.Injective
  row_spec (i₁ i₂) : ∑ j, T (i₁, j) = ∑ j, T (i₂, j)
  col_spec (j₁ j₂) : ∑ i, T (i, j₁) = ∑ i, T (i, j₂)


namespace IsGoodTable

/-- Any `1 × 1` table is a good table. -/
theorem of_const (α) : IsGoodTable (λ _ : Fin 1 × Fin 1 ↦ α) where
  injective := Function.injective_of_subsingleton _
  row_spec _ _ := rfl
  col_spec _ _ := rfl

/-- Swapping rows with column results in a good table. -/
theorem row_col_swap (hT : IsGoodTable T) : IsGoodTable (T ∘ Prod.swap) where
  injective := hT.injective.comp Prod.swap_injective
  row_spec := hT.col_spec
  col_spec := hT.row_spec

/-- If a (non-empty) good table has one row, it also has one column. -/
theorem num_cols_eq_one_of_num_rows_eq_one
    {T : Fin 1 × Fin (c + 1) → ℕ} (hT : IsGoodTable T) : c = 0 := by
  ---- Indeed, since the table has one row, by column sum, all entries are equal.
  have h : T (0, 1) = T (0, 0) := hT.col_spec 1 0
  replace h : (1 : Fin (c + 1)) = 0 := (Prod.mk_inj.mp (hT.injective h)).2
  rwa [Fin.one_eq_zero_iff, Nat.succ_inj] at h

open Finset in
/-- if a (non-empty) good table has at least two rows, then the sum of a column
  is less than the number of rows time the maximum of that column. -/
theorem sum_col_lt_num_rows_mul_max_col
    {T : Fin (r + 1) × Fin (c + 1) → ℕ} (hT : IsGoodTable T) (hr : r > 0) (j) :
    ∑ i, T (i, j) < (r + 1) * sup univ (λ i ↦ T (i, j)) :=
  let f (i : Fin (r + 1)) : ℕ := T (i, j)
  calc ∑ i, T (i, j)
  _ < ∑ i : Fin (r + 1), sup univ f := by
    -- It suffices to show that one of the entries is less than the maximum.
    refine sum_lt_sum (λ i _ ↦ le_sup (f := f) (mem_univ i)) ?_
    -- Since `1 ≠ 0`, one of `T(0, j₂)` and `T(1, j₂)` is less than the other.
    obtain h | h : f 1 < f 0 ∨ f 0 < f 1 := by
      refine Nat.lt_or_gt_of_ne λ (h : f 1 = f 0) ↦ ?_
      replace h : (1 : Fin (r + 1)) = 0 := (Prod.mk_inj.mp (hT.injective h)).1
      rw [Fin.one_eq_zero_iff, Nat.add_eq_right] at h
      exact hr.ne.symm h
    -- Either way one of `T(0, j₂)` and `T(1, j₂)` is less than the maximum.
    all_goals exact ⟨_, mem_univ _, h.trans_le (le_sup (mem_univ _))⟩
  _ = (r + 1) * sup univ f := by
    rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end IsGoodTable



/-- A finite nonempty set of positive integers must contain an
  element greater than or equal to its cardinality. -/
theorem exists_mem_ge_card {S : Finset ℕ} (hS : S.Nonempty) (hS0 : 0 ∉ S) :
    ∃ s ∈ S, s ≥ #S := by
  by_contra! h
  replace h : S ⊆ (range #S).erase 0 :=
    subset_erase.mpr ⟨λ s hs ↦ mem_range.mpr (h s hs), hS0⟩
  replace h : #S < #S := calc
    #S ≤ #((range #S).erase 0) := card_le_card h
    _ < #(range #S) := card_erase_lt_of_mem (by rwa [mem_range, card_pos])
    _ = #S := card_range _
  exact h.ne rfl

/-- An injective function `f : Fin (r + 1) → ℕ` attaining only positive values
  must attain a value greater than or equal to `r + 1`. -/
theorem Fin_exists_map_ge_dim
    {f : Fin (r + 1) → ℕ} (hf : f.Injective) (hf0 : ∀ i, f i ≠ 0) :
    ∃ i, f i ≥ r + 1 := by
  obtain ⟨n, hn, hn0⟩ : ∃ n ∈ image f univ, n ≥ #(image f univ) := by
    refine exists_mem_ge_card (image_nonempty.mpr univ_nonempty) ?_
    rw [mem_image, not_exists]
    intro i hi; exact hf0 i hi.2
  obtain ⟨i, -, rfl⟩ : ∃ i ∈ univ, f i = n := mem_image.mp hn
  rw [card_image_of_injective _ hf, card_fin] at hn0
  exact ⟨i, hn0⟩

/-- An injective function `f : Fin (r + 1) → ℕ` attaining only positive divisors of
  a positive integer `n` must attain a value at most `n/(r + 1)`. -/
theorem Fin_exists_map_le_div
    (hn : n ≠ 0) {f : Fin (r + 1) → ℕ} (hf : f.Injective) (hf0 : ∀ i, f i ∣ n) :
    ∃ i, (r + 1) * f i ≤ n := by
  let g (i) : ℕ := n / f i
  have hg : g.Injective :=
    λ i j h ↦ hf ((Nat.div_eq_iff_eq_of_dvd_dvd hn (hf0 i) (hf0 j)).mp h)
  have hg0 (i) : g i ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨ne_zero_of_dvd_ne_zero hn (hf0 i),
      Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hn) (hf0 i)⟩
  obtain ⟨i, hi⟩ : ∃ i, g i ≥ r + 1 := Fin_exists_map_ge_dim hg hg0
  exact ⟨i, Nat.mul_le_of_le_div (f i) (r + 1) n hi⟩

/-- Final solution -/
theorem final_solution :
    (∃ r c, ∃ T : Fin (r + 1) × Fin (c + 1) → ℕ,
        IsGoodTable T ∧ image T univ = Nat.divisors n)
      ↔ n = 1 := by
  ---- The `←` direction is easy.
  refine ⟨?_, λ h ↦ ⟨0, 0, λ _ ↦ 1, IsGoodTable.of_const 1, h.symm ▸ rfl⟩⟩
  ---- For the other direction, WLOG let `T` have no more rows than columns.
  rintro ⟨r, c, T, hT, hTn⟩
  wlog hrc : r ≤ c generalizing r c T
  · refine this c r (T ∘ Prod.swap) hT.row_col_swap ?_ (Nat.le_of_not_ge hrc)
    rw [← hTn, ← image_image]
    exact congrArg (image T) (image_univ_equiv (Equiv.prodComm _ _))
  ---- If `T` has one row, then `n` has to be equal to `1`.
  obtain rfl | hr : r = 0 ∨ r > 0 := Nat.eq_zero_or_pos r
  · obtain rfl : c = 0 := hT.num_cols_eq_one_of_num_rows_eq_one
    rw [← Nat.divisors_card_eq_one_iff, ← hTn, card_image_of_injective _ hT.injective]; rfl
  ---- Now assume that `T` has at least two rows. First note that `n > 0`.
  have hn : n ≠ 0 := by
    rw [Ne, ← Nat.divisors_eq_empty, ← hTn, image_eq_empty, ← Ne, ← nonempty_iff_ne_empty]
    exact univ_nonempty
  ---- Let `p` be the coordinate of the cell containing `n`.
  obtain ⟨p, hp⟩ : ∃ p, T p = n := by
    rw [← Set.mem_range, ← mem_image_univ_iff_mem_range, hTn]
    exact Nat.mem_divisors_self n hn
  ---- Now find a column `j₀` whose maximum entry is `≤ n/#columns`.
  obtain ⟨j₀, hj₀⟩ : ∃ j, (c + 1) * sup univ (λ i ↦ T (i, j)) ≤ n := by
    -- Define the function `f(j) = max{T(i, j) : i}`.
    let f (j : Fin (c + 1)) : ℕ := sup univ (λ i ↦ T (i, j))
    change ∃ j, (c + 1) * f j ≤ n
    -- By property of `max`, for each `j`, there exists `i` such that `T(i, j) = f(i)`.
    have hf (j) : ∃ i, f j = T (i, j) := by
      obtain ⟨i, -, h0⟩ : ∃ i ∈ univ, f j = T (i, j) :=
        exists_mem_eq_sup _ univ_nonempty _
      exact ⟨i, h0⟩
    -- Since the entries of `T` are pairwise distinct, `f` is injective.
    have hf0 : f.Injective := by
      intro j₁ j₂ h
      obtain ⟨i₁, h₁⟩ : ∃ i₁, f j₁ = T (i₁, j₁) := hf j₁
      obtain ⟨i₂, h₂⟩ : ∃ i₂, f j₂ = T (i₂, j₂) := hf j₂
      rw [h₁, h₂] at h
      exact (Prod.mk_inj.mp (hT.injective h)).2
    -- By the property of `T`, all values of `f` divide `n`.
    have hf1 (j) : f j ∣ n := by
      obtain ⟨i, h⟩ : ∃ i, f j = T (i, j) := hf j
      exact h ▸ Nat.dvd_of_mem_divisors (hTn ▸ mem_image_of_mem _ (mem_univ _))
    -- By `Fin_exists_map_le_div`, we are done.
    exact Fin_exists_map_le_div hn hf0 hf1
  ---- The sum of column `j₀` is less than `n`, but the sum of column `j₁` is `≥ n`.
  have h0 : ∑ i, T (i, j₀) < ∑ i, T (i, p.2) :=
    calc ∑ i, T (i, j₀)
    _ < (r + 1) * sup univ (λ i ↦ T (i, j₀)) :=
      hT.sum_col_lt_num_rows_mul_max_col hr j₀
    _ ≤ (c + 1) * sup univ (λ i ↦ T (i, j₀)) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right hrc 1)
    _ ≤ n := hj₀
    _ = T p := hp.symm
    _ ≤ ∑ i, T (i, p.2) :=
      single_le_sum (f := λ i ↦ T (i, p.2)) (λ _ _ ↦ Nat.zero_le _) (mem_univ _)
  ---- Contradiction!
  exact absurd (hT.col_spec j₀ p.2) h0.ne
