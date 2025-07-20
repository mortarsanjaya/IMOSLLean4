/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# IMO 2021 A6 (P6)

Let $m ∈ ℕ$ and $a_0, a_1, …, a_{k - 1}$ be integers.
Suppose that there exists subsets $B_0, B_1, …, B_{m - 1}$ of $[k]$
  such that for each $i ∈ [m]$, $$ \sum_{j ∈ B_i} a_j = m^{i + 1}. $$
Prove that $k ≥ m/2$.
-/

namespace IMOSL
namespace IMO2021A6

open Finset

/-- If `c_0 + c_1 m + c_2 m^2 + … + c_n m^n = d_0 + d_1 m + d_2 m^2 + … + d_n m^n`
  for `0 ≤ c_0, c_1, …, c_n, d_1, …, d_n < m`, then `c_i = d_i` for each `i`. -/
lemma Fin_digits_map_injOn (m n : ℕ) :
    (Fintype.piFinset (λ _ : Fin n ↦ range m) : Set (Fin n → ℕ)).InjOn
      λ c : (i : Fin n) → ℕ ↦ ∑ i : Fin n, c i * m ^ i.1 := by
  simp only [Set.InjOn, mem_coe, Fintype.mem_piFinset, mem_range]
  ---- Discharge the case `m = 0`
  obtain rfl | hm : m = 0 ∨ m ≠ 0 := eq_or_ne m 0
  · rintro c hc _ - -; funext i
    exact absurd (hc i) (c i).not_lt_zero
  ---- Induction on `n`, discharging the base case immediately
  induction' n with n n_ih
  · rintro c - d - -; exact funext λ i ↦ absurd i.2 i.1.not_lt_zero
  /- Focus on the main case `m > 0`. The first step is to prove `c_0 = d_0`.
    Then we get `c_1 + c_2 m + … + c_n m^{n - 1} = d_1 + d_2 m + … + d_n m^{n - 1}`.
    By induction hypothesis, this gives `c_i = d_i` for all `0 < i ≤ n`. -/
  intro c hc d hd h
  replace h : c 0 + (∑ i : Fin n, c i.succ * m ^ i.1) * m
      = d 0 + (∑ i : Fin n, d i.succ * m ^ i.1) * m := by
    simp only [Fin.sum_univ_succ, Fin.val_succ, Nat.pow_succ, ← Nat.mul_assoc] at h
    rwa [Fin.val_zero, pow_zero, mul_one, mul_one, ← sum_mul, ← sum_mul] at h
  have h0 : c 0 = d 0 := by
    apply congrArg (· % m) at h
    rwa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hc 0),
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hd 0)] at h
  have h1 : ∑ i : Fin n, c i.succ * m ^ i.1 = ∑ i : Fin n, d i.succ * m ^ i.1 := by
    rwa [h0, Nat.add_right_inj, Nat.mul_left_inj hm] at h
  exact funext (Fin.cases h0 (congrFun (n_ih (λ i ↦ hc i.succ) (λ i ↦ hd i.succ) h1)))

lemma Fin_digits_map_injOn' (m n : ℕ) :
    (Fintype.piFinset (λ _ : Fin n ↦ range m) : Set (Fin n → ℕ)).InjOn
      λ c : (i : Fin n) → ℕ ↦ ∑ i : Fin n, c i * (m : ℤ) ^ (i.1 + 1) := by
  obtain rfl | hm : m = 0 ∨ 0 < m := m.eq_zero_or_pos
  · rintro c hc _ - -; funext i
    simp only [mem_coe, Fintype.mem_piFinset, mem_range] at hc
    exact absurd (hc i) (c i).not_lt_zero
  · intro c hc d hd h
    simp only [← Int.natCast_pow, ← Int.natCast_mul, Nat.pow_succ, ← Nat.mul_assoc] at h
    rw [← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_inj, ← sum_mul, ← sum_mul] at h
    refine Fin_digits_map_injOn m n hc hd (Nat.mul_right_cancel hm h)


variable [Fintype κ] [DecidableEq κ] {a : κ → ℤ}

/-- More general inequality -/
theorem general_ineq {B : Fin n → Finset κ} [∀ i j, Decidable (j ∈ B i)]
    {m : ℕ} (h : ∀ i : Fin n, (B i).sum a = m ^ (i.1 + 1)) :
    m ^ n ≤ (n * (m - 1) + 1) ^ Fintype.card κ := by
  ---- Start with partial calculation, reducing to inequality on set size
  calc
    _ = (Fintype.piFinset λ _ : Fin n ↦ range m).card := by
      rw [Fintype.card_piFinset, card_range, prod_const, card_univ, Fintype.card_fin]
    _ ≤ (Fintype.piFinset λ _ : κ ↦ range (n * (m - 1) + 1)).card := ?_
    _ = _ := by rw [Fintype.card_piFinset, card_range, prod_const, card_univ]
  ---- Exhibit a nice function and show that this induces the desired cardinality
  let f (c : (i : Fin n) → ℕ) (j : κ) : ℕ := (univ.filter (j ∈ B ·)).sum c
  refine Finset.card_le_card_of_injOn f ?_ ?_
  ---- `f` maps `Fin n → [m]` to `κ → [n(m - 1) + 1]`
  · simp only [Fintype.coe_piFinset, coe_range]
    rintro c hc j -; calc
      _ ≤ ∑ i ∈ univ.filter (j ∈ B ·), (m - 1) :=
        sum_le_sum λ i _ ↦ Nat.le_pred_of_lt (hc i trivial)
      _ = (univ.filter (j ∈ B ·)).card * (m - 1) := sum_const _
      _ ≤ Fintype.card (Fin n) * (m - 1) := Nat.mul_le_mul_right (m - 1) (card_le_univ _)
      _ = n * (m - 1) := by rw [Fintype.card_fin]
      _ < _ := Nat.lt_succ_self _
  ---- `f` is injective on `Fin n → [m]`
  · let g (α : (j : κ) → ℕ) : ℤ := ∑ j : κ, α j * a j
    suffices Set.InjOn (g ∘ f) ↑(Fintype.piFinset λ _ : Fin n ↦ range m)
      from λ c hc d hd h ↦ this hc hd (congrArg g h)
    suffices g ∘ f = λ c : (i : Fin n) → ℕ ↦ ∑ i : Fin n, c i * (m : ℤ) ^ (i.1 + 1)
      from this ▸ Fin_digits_map_injOn' m n
    funext c; calc
      _ = ∑ j : κ, (∑ i : Fin n, if j ∈ B i then c i else 0) * a j := by
        simp only [g, f, sum_filter, Function.comp_apply]
      _ = ∑ j : κ, ∑ i : Fin n, if j ∈ B i then c i * a j else 0 := by
        refine Fintype.sum_congr _ _ λ j ↦ ?_
        rw [Nat.cast_sum, sum_mul]
        refine Fintype.sum_congr _ _ λ i ↦ ?_
        rw [Nat.cast_ite, Nat.cast_zero, ite_mul, Int.zero_mul]
      _ = ∑ i : Fin n, ∑ j : κ, if j ∈ B i then c i * a j else 0 := sum_comm
      _ = ∑ i : Fin n, (c i : ℤ) * ∑ j ∈ B i, a j := by
        refine Fintype.sum_congr _ _ λ i ↦ ?_
        rw [← sum_filter, filter_mem_eq_inter, univ_inter, mul_sum]
      _ = _ := Fintype.sum_congr _ _ λ i ↦ congrArg (_ * ·) (h i)

/-- Final solution -/
theorem final_solution {a : κ → ℤ} {B : Fin m → Finset κ}
    [∀ i j, Decidable (j ∈ B i)] (h : ∀ i : Fin m, (B i).sum a = m ^ (i.1 + 1)) :
    m ≤ 2 * Fintype.card κ := by
  obtain rfl | rfl | h0 : m = 0 ∨ 1 = m ∨ 1 < m :=
    m.eq_zero_or_pos.imp_right Nat.eq_or_lt_of_le
  ---- Case 1: `m = 0`
  · exact Nat.zero_le _
  ---- Case 2: `m = 1`
  · rw [Nat.succ_le_iff, Nat.mul_pos_iff_of_pos_left Nat.two_pos, Fintype.card_pos_iff]
    suffices (B 0).Nonempty from this.elim λ i _ ↦ ⟨i⟩
    refine (B 0).eq_empty_or_nonempty.resolve_left λ h0 ↦ absurd (h 0) ?_
    rw [h0, sum_empty]; exact Int.zero_ne_one
  ---- Case 3: `m > 1`
  · rw [← Nat.pow_le_pow_iff_right h0, Nat.pow_mul]
    refine (general_ineq h).trans (Nat.pow_le_pow_left ?_ _)
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := Nat.exists_eq_add_of_le' h0.le
    rw [Nat.add_sub_cancel, Nat.pow_two, Nat.mul_succ, Nat.add_le_add_iff_left]
    exact Nat.le_add_left 1 k
