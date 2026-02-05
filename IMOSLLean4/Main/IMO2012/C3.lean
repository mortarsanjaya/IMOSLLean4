/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# IMO 2012 C3

Let $N$ be a positive integer.
For any subset $S ⊆ \{0, 1, …, 3N - 1\}^2$, let $T(S)$ denote the number of
  quadruples $(i_0, i_1, i_2, i_3) ∈ \{0, 1, …, 3N - 1\}^4$ such that
  $(i_0, i_1) ∈ S$ and $(i_0, i_3), (i_2, i_1) ∉ S$.
Find the maximum possible value of $T(S)$.

### Answer

$12N^4$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf).
-/

namespace IMOSL
namespace IMO2012C3

open Finset

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (ι × ι))

/-- The number `T(S)` for each subset `S ⊆ ι × ι`. -/
def T : ℕ := #{p : (ι × ι) × (ι × ι) | p.1 ∈ S ∧ (p.2.1, p.1.2) ∉ S ∧ (p.1.1, p.2.2) ∉ S}

/-- An alternate formula for `T(S)`. -/
theorem T_alt_formula : T S = ∑ p ∈ S, #{j | (p.1, j) ∉ S} * #{i | (i, p.2) ∉ S} :=
  calc #{p : (ι × ι) × (ι × ι) | p.1 ∈ S ∧ (p.2.1, p.1.2) ∉ S ∧ (p.1.1, p.2.2) ∉ S}
  _ = ∑ p : (ι × ι) × (ι × ι) with p.1 ∈ S ∧ (p.2.1, p.1.2) ∉ S ∧ (p.1.1, p.2.2) ∉ S, 1 :=
    card_eq_sum_ones _
  _ = ∑ p : (ι × ι) × (ι × ι),
        if p.1 ∈ S ∧ (p.2.1, p.1.2) ∉ S ∧ (p.1.1, p.2.2) ∉ S then 1 else 0 :=
    sum_filter _ _
  _ = ∑ p : ι × ι, ∑ q : ι × ι, if p ∈ S ∧ (q.1, p.2) ∉ S ∧ (p.1, q.2) ∉ S then 1 else 0 :=
    Fintype.sum_prod_type _
  _ = ∑ p ∈ S, ∑ q : ι × ι, if (q.1, p.2) ∉ S ∧ (p.1, q.2) ∉ S then 1 else 0 := by
    simp_rw [ite_and (_ ∈ S), sum_ite_irrel]
    rw [sum_const_zero, Fintype.sum_ite_mem]
  _ = ∑ p ∈ S, #{j | (p.1, j) ∉ S} * #{i | (i, p.2) ∉ S} := by
    refine sum_congr rfl λ p _ ↦ ?_
    rw [← sum_filter, ← card_eq_sum_ones, Nat.mul_comm,
      ← card_product, ← filter_product, univ_product_univ]

/-- The inequality `2T(S) ≤ ∑_i (|ι| - a_i) a_i^2 + ∑_j (|ι| - b_j) b_j^2`,
  where `a_i = #{j | (i, j) ∉ S}` and `b_j = #{i | (i, j) ∉ S}`. -/
theorem T_ineq1 :
    2 * T S ≤ ∑ i, #{j | (i, j) ∈ S} * #{j | (i, j) ∉ S} ^ 2
      + ∑ j, #{i | (i, j) ∈ S} * #{i | (i, j) ∉ S} ^ 2 :=
  calc 2 * T S
  _ = ∑ p ∈ S, 2 * (#{j | (p.1, j) ∉ S} * #{i | (i, p.2) ∉ S}) := by
    rw [T_alt_formula, mul_sum]
  _ = ∑ p ∈ S, 2 * #{j | (p.1, j) ∉ S} * #{i | (i, p.2) ∉ S} := by simp_rw [← Nat.mul_assoc]
  _ ≤ ∑ p ∈ S, (#{j | (p.1, j) ∉ S} ^ 2 + #{i | (i, p.2) ∉ S} ^ 2) :=
    sum_le_sum λ p _ ↦ two_mul_le_add_sq _ _
  _ = ∑ p ∈ S, #{j | (p.1, j) ∉ S} ^ 2 + ∑ p ∈ S, #{i | (i, p.2) ∉ S} ^ 2 :=
    sum_add_distrib
  _ = ∑ i, #{j | (i, j) ∈ S} * #{j | (i, j) ∉ S} ^ 2
      + ∑ j, #{i | (i, j) ∈ S} * #{i | (i, j) ∉ S} ^ 2 := by
    refine congrArg₂ _ ?_ ?_
    · have h (p : ι × ι) : p ∈ S ↔ p.1 ∈ univ ∧ p.2 ∈ ({j | (p.1, j) ∈ S} : Finset _) := by
        rw [mem_filter_univ, and_iff_right (mem_univ _)]
      exact (sum_finset_product S univ (λ i ↦ {j | (i, j) ∈ S}) h).trans
        (Fintype.sum_congr _ _ λ i ↦ sum_const_nat λ _ _ ↦ rfl)
    · have h (p : ι × ι) : p ∈ S ↔ p.2 ∈ univ ∧ p.1 ∈ ({i | (i, p.2) ∈ S} : Finset _) := by
        rw [mem_filter_univ, and_iff_right (mem_univ _)]
      exact (sum_finset_product_right S univ (λ j ↦ {i | (i, j) ∈ S}) h).trans
        (Fintype.sum_congr _ _ λ i ↦ sum_const_nat λ _ _ ↦ rfl)

/-- For any `a, b : ℕ`, we have `27ab^2 ≤ 4(a + b)^3`. -/
theorem AMGM3_ineq (a b : ℕ) : 27 * (a * b ^ 2) ≤ 4 * (a + b) ^ 3 :=
  have h : 2 * (2 * a) * b ≤ (2 * a) ^ 2 + b ^ 2 := two_mul_le_add_sq _ _
  calc 27 * (a * b ^ 2)
    _ = 11 * (a * b ^ 2) + 4 * b * (2 * (2 * a) * b) := by ring
    _ ≤ 11 * (a * b ^ 2) + 4 * b * ((2 * a) ^ 2 + b ^ 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _
    _ = a * (2 * (2 * a) * b) + (11 * (a * b ^ 2) + 12 * (a ^ 2 * b) + 4 * b ^ 3) := by ring
    _ ≤ a * ((2 * a) ^ 2 + b ^ 2) + (11 * (a * b ^ 2) + 12 * (a ^ 2 * b) + 4 * b ^ 3) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _
    _ = 4 * (a + b) ^ 3 := by ring

/-- The inequality `27 T(S) ≤ 4|ι|^4`. -/
theorem T_ineq2 : 27 * T S ≤ 4 * Fintype.card ι ^ 4 := by
  refine Nat.le_of_mul_le_mul_left ?_ Nat.two_pos
  calc 2 * (27 * T S)
    _ = 27 * (2 * T S) := Nat.mul_left_comm _ _ _
    _ ≤ 27 * (∑ i, #{j | (i, j) ∈ S} * #{j | (i, j) ∉ S} ^ 2
        + ∑ j, #{i | (i, j) ∈ S} * #{i | (i, j) ∉ S} ^ 2) :=
      Nat.mul_le_mul_left _ (T_ineq1 S)
    _ = ∑ i, 27 * (#{j | (i, j) ∈ S} * #{j | (i, j) ∉ S} ^ 2)
        + ∑ j, 27 * (#{i | (i, j) ∈ S} * #{i | (i, j) ∉ S} ^ 2) := by
      rw [Nat.mul_add, mul_sum, mul_sum]
    _ ≤ ∑ i, 4 * (#{j | (i, j) ∈ S} + #{j | (i, j) ∉ S}) ^ 3
        + ∑ j, 4 * (#{i | (i, j) ∈ S} + #{i | (i, j) ∉ S}) ^ 3 :=
      Nat.add_le_add (sum_le_sum λ _ _ ↦ AMGM3_ineq _ _)
        (sum_le_sum λ _ _ ↦ AMGM3_ineq _ _)
    _ = 2 * (4 * Fintype.card ι ^ 4) := by
      simp_rw [card_filter_add_card_filter_not]
      rw [← Nat.two_mul, sum_const, card_univ,
        Nat.pow_succ' (n := 3), Nat.mul_left_comm 4]; rfl

/-- Given a bijection `e : ι ≃ κ`, we have `T({(e(i), e(j)) : (i, j) ∈ S}) = T(S)`. -/
theorem T_image_equiv [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    T (S.image (e.prodCongr e)) = T S := by
  set e₂ := e.prodCongr e
  set S₂ := S.image e₂
  refine (card_equiv (e₂.prodCongr e₂) ?_).symm
  rintro ⟨⟨i₀, i₁⟩, ⟨i₂, i₃⟩⟩
  iterate 2 rw [mem_filter_univ]
  change (i₀, i₁) ∈ S ∧ (i₂, i₁) ∉ S ∧ (i₀, i₃) ∉ S
    ↔ e₂ (i₀, i₁) ∈ S₂ ∧ e₂ (i₂, i₁) ∉ S₂ ∧ e₂ (i₀, i₃) ∉ S₂
  refine and_congr ?_ (and_congr ?_ ?_)
  all_goals simp only [S₂, mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]

end


/-- Let `S ⊆ κ × κ`, and define `S' = {(k, i, l, j) : (k, l) ∈ S} ⊆ (κ × ι) × (κ × ι)`.
  Then `T(S') = T(S) |ι|^4`. -/
theorem T_product_univ_right
    [Fintype κ] [DecidableEq κ] (S : Finset (κ × κ)) (ι) [Fintype ι] [DecidableEq ι] :
    T {p : (κ × ι) × (κ × ι) | (p.1.1, p.2.1) ∈ S} = T S * Fintype.card ι ^ 4 :=
  calc T {p : (κ × ι) × (κ × ι) | (p.1.1, p.2.1) ∈ S}
    _ = #{p : ((κ × ι) × (κ × ι)) × ((κ × ι) × (κ × ι)) |
          (p.1.1.1, p.1.2.1) ∈ S ∧ (p.2.1.1, p.1.2.1) ∉ S ∧ (p.1.1.1, p.2.2.1) ∉ S} := by
      simp_rw [T, mem_filter_univ]
    _ = #{p : ((κ × κ) × (κ × κ)) × ((ι × ι) × (ι × ι)) |
          p.1.1 ∈ S ∧ (p.1.2.1, p.1.1.2) ∉ S ∧ (p.1.1.1, p.1.2.2) ∉ S} := by
      let e := Equiv.prodProdProdComm κ ι κ ι
      refine card_equiv ((e.prodCongr e).trans (Equiv.prodProdProdComm _ _ _ _)) λ i ↦ ?_
      rw [mem_filter_univ, mem_filter_univ]; rfl
    _ = T S * Fintype.card ((ι × ι) × (ι × ι)) := by
      rw [← card_univ, T, ← card_product]
      refine congrArg card (ext λ i ↦ ?_)
      rw [mem_filter_univ, mem_product, mem_filter_univ, and_iff_left (mem_univ _)]
    _ = T S * Fintype.card ι ^ 4 := by
      rw [Fintype.card_prod, Fintype.card_prod, ← Nat.pow_two, ← Nat.pow_two, ← Nat.pow_mul]

/-- If `S ⊆ Fin 3 × Fin 3` is the diagonal, then `T(S) = 12`. -/
theorem T_Fin3_diag : T (diag univ : Finset (Fin 3 × Fin 3)) = 12 := by
  simp_rw [T, mem_diag, mem_univ, true_and]; rfl

/-- If `S ⊆ (Fin 3 × ι) × (Fin 3 × ι)` is defined by
  `S = {(m, i, n, j) : m = n}`, then `T(S) = 12|ι|^4`. -/
theorem T_Fin3_diag_product (ι) [Fintype ι] [DecidableEq ι] :
    T {p : (Fin 3 × ι) × (Fin 3 × ι) | (p.1.1, p.2.1) ∈ diag univ}
      = 12 * Fintype.card ι ^ 4 :=
  calc T {p : (Fin 3 × ι) × (Fin 3 × ι) | (p.1.1, p.2.1) ∈ diag univ}
  _ = T (diag univ : Finset (Fin 3 × Fin 3)) * Fintype.card ι ^ 4 :=
    T_product_univ_right {p : Fin 3 × Fin 3 | p.1 = p.2} ι
  _ = 12 * Fintype.card ι ^ 4 := congrArg (· * _) T_Fin3_diag

/-- Final solution -/
theorem final_solution (N) : IsGreatest (Set.range (T (ι := Fin (3 * N)))) (12 * N ^ 4) := by
  refine ⟨?_, ?_⟩
  ---- There exists a subset `S ⊆ Fin 3N × Fin 3N` with `T(S) = 12N^4`.
  · let κ := Fin 3 × Fin N
    obtain ⟨e⟩ : Nonempty (κ ≃ Fin (3 * N)) := by
      rw [← Fintype.card_eq, Fintype.card_prod]
      iterate 3 rw [Fintype.card_fin]
    use image (e.prodCongr e) {p : κ × κ | (p.1.1, p.2.1) ∈ diag univ}
    rw [T_image_equiv, T_Fin3_diag_product, Fintype.card_fin]
  ---- For any subset `S ⊆ Fin 3N × Fin 3N`, we have `T(S) ≤ 12N^4`.
  · rintro _ ⟨S, rfl⟩
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos 26 : 0 < 27)
    calc 27 * T S
      _ ≤ 4 * (Fintype.card (Fin (3 * N))) ^ 4 := T_ineq2 S
      _ = 4 * 3 ^ 4 * N ^ 4 := by rw [Fintype.card_fin, Nat.mul_pow, Nat.mul_assoc]
      _ = 27 * (12 * N ^ 4) := Nat.mul_assoc 27 12 _
