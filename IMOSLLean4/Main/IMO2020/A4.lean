/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Analysis.MeanInequalities

/-!
# IMO 2020 A4 (P2)

Let $a, b, c, d ∈ ℝ$ with $a ≥ b ≥ c ≥ d > 0$ and $a + b + c + d = 1$.
Prove that $$ (a + 2b + 3c + 4d) a^a b^b c^c d^d < 1. $$

### Solution

We follow both Solution 1 and Solution of the
  [official solution](https://www.imo-official.org/problems/IMO2020SL.pdf).
We start with $a + 2b + 3c + 4d ≤ a + 3(b + c + d) = 3 - 2a$.
Then we use the bound $a^a b^b c^c d^d ≤ a$ when $a < 1/2$ and the weighted AM-GM
  $a^a b^b c^c d^d ≤ a^2 + b^2 + c^2 + d^2$ when $1/2 ≤ a < 1$.
-/

namespace IMOSL
namespace IMO2020A4

open Finset Real

section

variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]

/-- If `a, b > 0` then` a^2 + b^2 < (a + b)^2`. -/
theorem sq_add_lt_add_sq {a b : R} (ha : a > 0) (hb : b > 0) :
    a ^ 2 + b ^ 2 < (a + b) ^ 2 := by
  rw [add_sq', lt_add_iff_pos_right]
  exact mul_pos (mul_pos two_pos ha) hb

/-- If `n ≥ 2` and `x_1, x_2, …, x_n > 0`, then `∑_i x_i^2 < (∑_i x_i)^2`. -/
theorem sum_sq_lt_sq_sum_of_pos [DecidableEq ι] {f : ι → R} {I : Finset ι}
    (hI : #I ≥ 2) (hf : ∀ i ∈ I, 0 < f i) :
    ∑ i ∈ I, f i ^ 2 < (∑ i ∈ I, f i) ^ 2 := by
  obtain ⟨i₀, hi₀⟩ : I.Nonempty := card_pos.mp (Nat.zero_lt_of_lt hI)
  replace hI : (I.erase i₀).Nonempty :=
    card_pos.mp ((Nat.sub_le_sub_right hI 1).trans pred_card_le_card_erase)
  have hf' (i) (hi : i ∈ I.erase i₀) : 0 < f i := hf i (mem_of_mem_erase hi)
  calc ∑ i ∈ I, f i ^ 2
    _ = f i₀ ^ 2 + ∑ i ∈ I.erase i₀, f i ^ 2 := (add_sum_erase _ _ hi₀).symm
    _ ≤ f i₀ ^ 2 + (∑ i ∈ I.erase i₀, f i) ^ 2 :=
      add_le_add_right (sum_sq_le_sq_sum_of_nonneg λ i hi ↦ (hf' i hi).le) _
    _ < (f i₀ + ∑ i ∈ I.erase i₀, f i) ^ 2 :=
      sq_add_lt_add_sq (hf i₀ hi₀) (sum_pos hf' hI)
    _ = (∑ i ∈ I, f i) ^ 2 := by rw [add_sum_erase _ _ hi₀]

end



/-- A general inequality: if `n ≥ 3` and `x_1, x_2, …, x_n` are positive real
  numbers with `x_1 ≥ x_i` for each `i` and `x_1 + x_2 + … + x_n = 1`,
  then `(3 - 2x_1) x_1^{x_1} … x_n^{x_n} < 1`. -/
theorem general_ineq [DecidableEq ι] {I : Finset ι} (hI : #I ≥ 3)
    {x : ι → ℝ} (hxI : ∀ i ∈ I, x i > 0) {i₀ : ι} (hi₀ : i₀ ∈ I)
    (hxI0 : ∀ i ∈ I, x i ≤ x i₀) (hxI1 : ∑ i ∈ I, x i = 1) :
    (3 - 2 * x i₀) * ∏ i ∈ I, x i ^ x i < 1 := by
  ---- For convenience, let `a = x_{i₀}`.
  let a : ℝ := x i₀
  ---- We prove a bunch of inequalities before dividing into cases...
  have hxI' (i) (hi : i ∈ I) : x i ≥ 0 :=
    (hxI i hi).le
  have hI0 : #(I.erase i₀) ≥ 2 := calc
    3 - 1 ≤ #I - 1 := Nat.sub_le_sub_right hI 1
    _ ≤ #(I.erase i₀) := pred_card_le_card_erase
  have hxI'' (i) (hi : i ∈ I.erase i₀) : x i > 0 :=
    hxI i (mem_of_mem_erase hi)
  have ha : a < 1 := calc
    a < a + ∑ i ∈ I.erase i₀, x i :=
      lt_add_of_pos_right a (sum_pos hxI'' (card_pos.mp (Nat.zero_lt_of_lt hI0)))
    _ = 1 := by rw [add_sum_erase I x hi₀, hxI1]
  have ha0 : 0 < 3 - 2 * a := calc
    0 < 2 * (1 - a) := mul_pos two_pos (sub_pos_of_lt ha)
    _ = 2 - 2 * a := mul_one_sub _ _
    _ < 3 - 2 * a := sub_lt_sub_right (by norm_num) _
  ---- Split into cases `a < 1/2` and `a ≥ 1/2`.
  obtain ha1 | ha1 : 2 * a < 1 ∨ 1 ≤ 2 * a := lt_or_ge _ _
  ---- If `a < 1/2`, then `∏_i x_i^{x_i} ≤ a` and `(3 - 2a) a < 1`.
  · have h : ∏ i ∈ I, x i ^ x i ≤ a := calc
      _ ≤ ∏ i ∈ I, a ^ x i :=
        prod_le_prod (λ i hi ↦ rpow_nonneg (hxI' i hi) _)
          (λ i hi ↦ rpow_le_rpow (hxI' i hi) (hxI0 i hi) (hxI' i hi))
      _ = a := by rw [← rpow_sum_of_pos (hxI _ hi₀), hxI1, rpow_one]
    calc (3 - 2 * a) * ∏ i ∈ I, x i ^ x i
      _ ≤ (3 - 2 * a) * a := mul_le_mul_of_nonneg_left h ha0.le
      _ = 1 - (1 - 2 * a) * (1 - a) := by ring
      _ < 1 := sub_lt_self 1 (mul_pos (sub_pos_of_lt ha1) (sub_pos_of_lt ha))
  /- If `1/2 ≤ a < 1`, then `∏_i x_i^{x_i} ≤ ∑_i x_i^{x_i} < a^2 + (1 - a)^2`
    and `(3 - 2a)(a^2 + (1 - a)^2) ≤ 1`. -/
  · have h : ∏ i ∈ I, x i ^ x i < a ^ 2 + (1 - a) ^ 2 := calc
      _ ≤ ∑ i ∈ I, x i * x i := geom_mean_le_arith_mean_weighted I x x hxI' hxI1 hxI'
      _ = ∑ i ∈ I, x i ^ 2 := by simp only [sq]
      _ = a ^ 2 + ∑ i ∈ I.erase i₀, x i ^ 2 := (add_sum_erase _ _ hi₀).symm
      _ < a ^ 2 + (∑ i ∈ I.erase i₀, x i) ^ 2 :=
        add_lt_add_right (sum_sq_lt_sq_sum_of_pos hI0 hxI'') _
      _ = a ^ 2 + (1 - a) ^ 2 := by rw [sum_erase_eq_sub hi₀, hxI1]
    calc (3 - 2 * a) * ∏ i ∈ I, x i ^ x i
      _ < (3 - 2 * a) * (a ^ 2 + (1 - a) ^ 2) :=
        mul_lt_mul_of_pos_left h ha0
      _ = 1 - 2 * ((1 - a) ^ 2 * (2 * a - 1)) := by ring
      _ ≤ 1 := sub_le_self 1 <| mul_nonneg zero_le_two <|
        mul_nonneg (sq_nonneg _) (sub_nonneg_of_le ha1)

/-- Final solution -/
theorem final_solution {a b c d : ℝ}
    (hd : d > 0) (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a) (h : a + b + c + d = 1) :
    (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) < 1 :=
  ---- First define `x_0 = a, x_1 = b, x_2 = c, x_3 = d`, and prove some properties.
  let x : Fin 4 → ℝ := ![a, b, c, d]
  have hx (i) : x i > 0 :=
    have hc : c > 0 := hd.trans_le hdc
    have hb : b > 0 := hc.trans_le hcb
    have ha : a > 0 := hb.trans_le hba
    match i with | 0 => ha | 1 => hb | 2 => hc | 3 => hd
  have hdb : d ≤ b := hdc.trans hcb
  have hx0 (i) : x i ≤ x 0 :=
    match i with | 0 => le_refl a | 1 => hba | 2 => hcb.trans hba | 3 => hdb.trans hba
  ---- Now do the calculations.
  calc (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d)
  _ = (a + (3 * b - b) + 3 * c + (3 * d + d)) * ∏ i : Fin 4, x i ^ x i := by
    rw [Fin.prod_univ_four, eq_sub_of_add_eq (G := ℝ) two_add_one_eq_three,
      ← three_add_one_eq_four, sub_one_mul, add_one_mul]; rfl
  _ = (a + 3 * (b + c + d) + d - b) * ∏ i : Fin 4, x i ^ x i := by
    rw [mul_add, mul_add, add_sub_right_comm, add_sub_assoc a, add_sub_right_comm,
      add_sub_right_comm, ← add_assoc, add_assoc a, add_assoc a]
  _ ≤ (a + 3 * (b + c + d) + d - d) * ∏ i : Fin 4, x i ^ x i :=
    mul_le_mul_of_nonneg_right (sub_le_sub_left hdb _)
      (prod_nonneg λ i _ ↦ rpow_nonneg (hx i).le _)
  _ ≤ ((3 - 2) * a + 3 * (b + c + d)) * ∏ i : Fin 4, x i ^ x i := by
    rw [add_sub_cancel_right, sub_eq_of_eq_add' (G := ℝ) two_add_one_eq_three.symm, one_mul]
  _ = (3 - 2 * x 0) * ∏ i : Fin 4, x i ^ x i := by
    rw [sub_mul, ← add_sub_right_comm, ← mul_add, ← add_assoc, ← add_assoc, h, mul_one]; rfl
  _ < 1 :=
    have h0 : #(univ : Finset (Fin 4)) ≥ 3 := Nat.le_succ 3
    general_ineq h0 (λ i _ ↦ hx i) (mem_univ _)
      (λ i _ ↦ hx0 i) ((Fin.sum_univ_four _).trans h)
