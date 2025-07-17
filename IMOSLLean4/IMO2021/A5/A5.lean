/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Field.Basic

/-!
### IMO 2021 A5

Let $F$ be a totally ordered field.
Let $a_1, a_2, …, a_n ∈ F$ be non-negative elements.
Let $r ∈ F$ be any positive element such that $r ≥ a_1 + a_2 + … + a_n$.
Prove that
$$ \sum_{k = 1}^n \frac{a_k}{r - a_k} (a_1 + a_2 + … + a_{k - 1})^2 < \frac{r^2}{3}. $$
-/

namespace IMOSL
namespace IMO2021A5

def targetSumPair [Field F] (r : F) (l : List F) : F × F :=
  l.foldr (λ a p ↦ (a / (r - a) * p.2 ^ 2 + p.1, a + p.2)) (0, 0)





/-! ### Some identities and inequalities -/

section

variable [AddCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M] {l : List M} (hl : ∀ x ∈ l, 0 ≤ x)
include hl

lemma foldr_add_nonneg : 0 ≤ l.foldr (· + ·) 0 := by
  induction' l with a l l_ih
  · exact le_refl 0
  · replace hl : 0 ≤ a ∧ ∀ x ∈ l, 0 ≤ x := List.forall_mem_cons.mp hl
    exact add_nonneg hl.1 (l_ih hl.2)

lemma foldr_add_pos (hl0 : ∃ x ∈ l, x ≠ 0) : 0 < l.foldr (· + ·) 0 := by
  induction' l with a l l_ih
  · exact hl0.elim λ c h ↦ absurd h.1 List.not_mem_nil
  · replace hl : 0 ≤ a ∧ ∀ x ∈ l, 0 ≤ x := List.forall_mem_cons.mp hl
    simp only [List.mem_cons, exists_eq_or_imp] at hl0
    rcases hl0 with h | h
    exacts [add_pos_of_pos_of_nonneg (hl.1.lt_of_ne h.symm) (foldr_add_nonneg hl.2),
      (add_pos_of_pos_of_nonneg (l_ih hl.2 h) hl.1).trans_eq (add_comm _ _)]

end


lemma ring_id [CommRing R] (x y : R) :
    (x + y) ^ 3 - x ^ 3 - y ^ 3 = 3 * (x * y * (x + y)) := calc
  _ = (x ^ 2 + y ^ 2) * (x + y) - (x ^ 3 + y ^ 3) + 2 * (x * y * (x + y)) := by
    rw [pow_succ, add_sq', sub_sub, add_mul, add_sub_right_comm, mul_assoc 2, mul_assoc]
  _ = x ^ 2 * y + y ^ 2 * x + 2 * (x * y * (x + y)) := by
    refine congrArg₂ _ ?_ rfl
    rw [add_mul, mul_add, mul_add, add_assoc, ← pow_succ, ← pow_succ,
      add_sub_add_left_eq_sub, ← add_assoc, add_sub_cancel_right]
  _ = x * y * (x + y) + 2 * (x * y * (x + y)) := by
    rw [sq, sq, mul_right_comm, ← mul_rotate x y y, ← mul_add]
  _ = _ := by rw [← one_add_mul, add_comm, two_add_one_eq_three]

lemma field_ineq [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {r : F} (ha : 0 ≤ a) (hs : 0 ≤ s) (h : a + s ≤ r) :
    a / (r - a) * s ^ 2 ≤ ((a + s) ^ 3 - s ^ 3 - a ^ 3) / (3 * r) := calc
  _ = a * s * (s / (r - a)) := by rw [sq, ← mul_div_right_comm, ← mul_assoc, mul_div_assoc]
  _ ≤ a * s * ((a + s) / r) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg ha hs)
    obtain rfl | h0 : a = r ∨ a < r := (le_of_add_le_of_nonneg_left h hs).eq_or_lt
    · rw [sub_self, div_zero]; exact div_nonneg (add_nonneg ha hs) ha
    · rw [div_le_div_iff₀ (sub_pos_of_lt h0) (ha.trans_lt h0), add_mul, mul_sub s,
        add_sub_left_comm, le_add_iff_nonneg_right, mul_comm a, ← sub_mul, sub_sub]
      exact mul_nonneg (sub_nonneg_of_le h) ha
  _ = _ := by rw [sub_right_comm, ring_id, mul_div_mul_left _ _ three_ne_zero, mul_div_assoc]





/-! ### Start of the problem -/

section

variable [Field F] (r : F)

lemma targetSumPair_nil : targetSumPair r [] = (0, 0) := rfl

lemma targetSumPair_cons_fst (a l) :
    (targetSumPair r (a :: l)).1 =
      a / (r - a) * (targetSumPair r l).2 ^ 2 + (targetSumPair r l).1 := rfl

lemma targetSumPair_cons_snd (a l) :
    (targetSumPair r (a :: l)).2 = a + (targetSumPair r l).2 := rfl

lemma targetSumPair_snd_eq : ∀ l : List F, (targetSumPair r l).2 = l.foldr (· + ·) 0
  | [] => rfl
  | a :: l => by rw [List.foldr, targetSumPair_cons_snd, targetSumPair_snd_eq]

lemma targetSumPair_replicate_zero : ∀ n, targetSumPair r (List.replicate n 0) = (0, 0)
  | 0 => rfl
  | n + 1 => by rw [targetSumPair, List.replicate_succ, List.foldr_cons,
    ← targetSumPair, targetSumPair_replicate_zero n, zero_div, zero_mul, zero_add]


theorem targetSumPair_main_ineq [LinearOrder F] [IsStrictOrderedRing F] {l : List F}
    (hl : ∀ x ∈ l, 0 ≤ x) {r : F} (hr : l.foldr (· + ·) 0 ≤ r) :
    (targetSumPair r l).1 ≤ ((l.foldr (· + ·) 0) ^ 3 - l.foldr (· ^ 3 + ·) 0) / (3 * r) := by
  induction' l with a l l_ih generalizing r
  · rw [List.foldr, List.foldr, sub_zero, pow_succ', zero_mul, zero_div, targetSumPair_nil]
  · replace hl : 0 ≤ a ∧ ∀ x ∈ l, 0 ≤ x := List.forall_mem_cons.mp hl
    let s : F := (targetSumPair r l).2
    have h : s = l.foldr (· + ·) 0 := targetSumPair_snd_eq r l
    calc
      _ = a / (r - a) * s ^ 2 + (targetSumPair r l).1 := rfl
      _ ≤ ((a + s) ^ 3 - s ^ 3 - a ^ 3) / (3 * r) +
          (s ^ 3 - l.foldr (· ^ 3 + ·) 0) / (3 * r) :=
        add_le_add (field_ineq hl.1 ((foldr_add_nonneg hl.2).trans_eq h.symm) (h ▸ hr))
          (h ▸ l_ih hl.2 (le_of_add_le_of_nonneg_right hr hl.1))
      _ = _ := by rw [← add_div, sub_sub, sub_add, add_sub_sub_cancel, h]; rfl

/-- Final solution -/
theorem final_solution [LinearOrder F] [IsStrictOrderedRing F] {r : F} (hr : 0 < r)
    (hl : ∀ x ∈ l, 0 ≤ x) (h : l.foldr (· + ·) 0 ≤ r) :
    (targetSumPair r l).1 < r ^ 2 / 3 := by
  have X : 0 < (3 : F) := three_pos
  by_cases h0 : ∀ x ∈ l, x = 0
  ---- Case 1: `l` consists of zeroes
  · rw [List.eq_replicate_of_mem h0, targetSumPair_replicate_zero]
    exact div_pos (pow_pos hr 2) X
  ---- Case 2: `l` contains a positive element
  · replace X : 0 < 3 * r := mul_pos X hr
    suffices 0 < (l.map (· ^ 3)).foldr (· + ·) 0 by calc
      _ ≤ ((l.foldr (· + ·) 0) ^ 3 - l.foldr (· ^ 3 + ·) 0) / (3 * r) := by
        exact targetSumPair_main_ineq hl h
      _ < (l.foldr (· + ·) 0) ^ 3 / (3 * r) := by
        refine div_lt_div_of_pos_right ?_ X
        rwa [sub_lt_self_iff, ← l.foldr_map]
      _ ≤ r ^ 3 / (3 * r) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (foldr_add_nonneg hl) h 3) X.le
      _ = r ^ 2 / 3 := by rw [pow_succ, mul_div_mul_right _ _ hr.ne.symm]
    -- Finally, prove that `0 < ∑ a_i^3`
    apply foldr_add_pos
    · simp only [List.mem_map]; rintro _ ⟨a, ha, rfl⟩
      exact pow_nonneg (hl a ha) 3
    · simp only [not_forall] at h0
      rcases h0 with ⟨a, ha, h0⟩
      exact ⟨a ^ 3, List.mem_map_of_mem ha, pow_ne_zero 3 h0⟩
