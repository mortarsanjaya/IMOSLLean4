/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2013.A5.FinChainFn

/-!
# IMO 2013 A5

Find all functions $f : ℕ → ℕ$ such that, for any $n ∈ ℕ$,
$$ f(f(f(n))) = f(n + 1) + 1. $$
-/

namespace IMOSL
namespace IMO2013A5

open Finset
open scoped Classical

/-- (+4)-induction -/
theorem add_four_induction {P : ℕ → Prop}
    (h : P 0) (h0 : P 1) (h1 : P 2) (h2 : P 3)
    (h3 : ∀ n, P n → P (n + 4)) : ∀ n, P n
  | 0 => h
  | 1 => h0
  | 2 => h1
  | 3 => h2
  | n + 4 => h3 n (add_four_induction h h0 h1 h2 h3 n)



/-! ### Start of the problem -/

def good (f : ℕ → ℕ) := ∀ n, f^[3] n = f (n + 1) + 1

/-- The second class of answer -/
def answer2 : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 3
  | 3 => 0
  | n + 4 => answer2 n + 4

theorem good_succ : good Nat.succ := λ _ ↦ rfl

theorem good_answer2 : good answer2
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => congr_arg (· + 4) (good_answer2 n)



section Solution

variable (h : good f)
include h

theorem iter_four_eq : ∀ n, f^[4] n = f^[4] 0 + n :=
  have h0 n : f^[4] (n + 1) = f^[4] n + 1 := by
    rw [f.iterate_succ_apply, h, ← h n, ← f.iterate_succ_apply']
  Nat.rec rfl λ n h1 ↦ by rw [Nat.add_succ, h0, h1]

theorem good_injective : f.Injective :=
  suffices f^[4].Injective from this.of_comp
  λ m n h0 ↦ by rwa [iter_four_eq h, iter_four_eq h n, add_right_inj] at h0

noncomputable def finChainFnOfgood : FinChainFn f where
  injective' := good_injective h
  rangeCompl' := (range (f^[4] 0)).filter (· ∉ Set.range f)
  rangeCompl_spec' := Set.ext λ n ↦ by
    rw [mem_coe, mem_filter, mem_range, ← not_le]
    refine and_iff_right_of_imp λ h0 h1 ↦ h0 ⟨f^[3] (n - f^[4] 0), ?_⟩
    rw [← f.iterate_succ_apply', iter_four_eq h, Nat.add_sub_of_le h1]

theorem iterRangeCompl_three_subset :
    (finChainFnOfgood h).iterRangeCompl 3 ⊆
      {0, (f 0).succ} ∪ image Nat.succ (finChainFnOfgood h).rangeCompl := by
  intro x h0
  rw [mem_union, mem_image, mem_insert, mem_singleton, or_assoc]
  refine x.eq_zero_or_eq_succ_pred.imp id λ h1 ↦ ?_
  generalize x.pred = c at h1; subst h1
  refine (em <| c ∈ Set.range f).imp (λ h1 ↦ ?_) (λ h1 ↦ ⟨c, ?_, rfl⟩)
  · rcases h1 with ⟨d, rfl⟩
    refine d.eq_zero_or_eq_succ_pred.elim (λ h2 ↦ h2 ▸ rfl) (λ h2 ↦ ?_)
    rw [(finChainFnOfgood h).mem_iterRangeCompl_iff] at h0
    refine absurd ⟨d.pred, ?_⟩ h0
    rw [h, ← d.pred.succ_eq_add_one, ← h2]
  · rwa [(finChainFnOfgood h).mem_rangeCompl_iff]

theorem exists_rangeCompl_eq_singleton :
    ∃ a, (finChainFnOfgood h).rangeCompl = {a} := by
  have h0 := (card_le_card <| iterRangeCompl_three_subset h).trans <|
    (card_union_le _ _).trans <| Nat.add_le_add
      (card_pair (f 0).succ_ne_zero.symm).le card_image_le
  rw [(finChainFnOfgood h).iterRangeCompl_card, Nat.succ_mul,
    Nat.add_le_add_iff_right, mul_comm, ← Nat.le_div_iff_mul_le (Nat.succ_pos 1)] at h0
  refine h0.eq_or_lt.elim card_eq_one.mp (λ h0 ↦ ?_)
  rw [Nat.lt_one_iff, card_eq_zero, ← (finChainFnOfgood h).surjective_iff] at h0
  obtain ⟨a, h0⟩ := h0.iterate 3 0
  exact absurd ((h a).symm.trans h0) (f a.succ).succ_ne_zero

theorem iter_four_zero_eq_four : f^[4] 0 = 4 := by
  obtain ⟨a, h0⟩ := exists_rangeCompl_eq_singleton h
  suffices (finChainFnOfgood h).iterRangeCompl 4 = range (f^[4] 0) by
    rw [← card_range (f^[4] 0), ← this,
      (finChainFnOfgood h).iterRangeCompl_card, h0, card_singleton]
  -- It remains to check that `f^[4](ℕ) = {4, 5, 6, …}`
  ext n; rw [(finChainFnOfgood h).mem_iterRangeCompl_iff, mem_range, not_iff_comm, not_lt]
  refine ⟨λ h1 ↦ ⟨n - f^[4] 0, ?_⟩, λ ⟨k, h1⟩ ↦ ?_⟩
  · rw [iter_four_eq h, Nat.add_sub_of_le h1]
  · rw [← h1, iter_four_eq h k]; exact Nat.le_add_right _ k

theorem iter_four_eq_add_four (n : ℕ) : f^[4] n = n + 4 := by
  rw [iter_four_eq h, add_comm, iter_four_zero_eq_four h]

theorem map_add_four (n : ℕ) : f (n + 4) = f n + 4 := by
  have h1 := iter_four_eq_add_four h
  rw [← h1, ← h1]; rfl

theorem good_imp_succ_or_answer2 : f = Nat.succ ∨ f = answer2 := by
  ---- Get `{a, f(a), f(f(a))} ⊆ {0, f(0) + 1, a + 1}`
  rcases exists_rangeCompl_eq_singleton h with ⟨a, h0⟩
  have h1 := iterRangeCompl_three_subset h
  let C := finChainFnOfgood h
  rw [C.iterRangeCompl_succ, C.iterRangeCompl_succ, C.iterRangeCompl_one] at h1
  unfold FinChainFn.exactIterRange at h1
  rw [h0, image_singleton, image_singleton, image_singleton, union_subset_iff,
    union_subset_iff, f.iterate_succ_apply, f.iterate_one] at h1
  iterate 3 rw [singleton_subset_iff, mem_union,
    mem_singleton, mem_insert, mem_singleton] at h1
  ---- Preparation for the subcases
  have h2 (n) : f (f n) ≠ n := λ h2 ↦ by
    apply absurd (iter_four_eq_add_four h n)
    change f (f (f (f n))) ≠ n + 4
    rw [h2, h2, left_ne_add]
    exact Nat.succ_ne_zero 3
  have h3 (n) : f n ≠ n := λ h3 ↦ h2 n (Function.iterate_fixed h3 2)
  rcases h1 with ⟨h1, h4, (rfl | rfl) | h5⟩
  ---- Case 1: `a = 0`
  · rw [or_iff_right (h3 0), or_iff_right (f 0).succ_ne_self.symm] at h4
    rw [or_iff_right (h2 0), h4, or_iff_left (h3 1)] at h1
    have h5 : f (f (f 0)) = f 1 + 1 := h 0
    have h6 : f (f (f (f 0))) = 4 := iter_four_zero_eq_four h
    rw [h5, h1] at h6
    rw [h4, h1] at h5
    left; refine funext (add_four_induction h4 h1 h5 h6 ?_)
    intro n h7; rw [map_add_four h, h7]
  ---- Case 2: `a = f(0) + 1`
  · rw [or_iff_left (h3 _)] at h4
    rw [or_iff_left (h2 _)] at h1
    rcases h4 with h4 | h4
    -- The impossible subcase `f(a) = 0`
    · rw [h4, or_iff_right (h3 0)] at h1
      exact absurd h1 (Nat.lt_succ.mpr (f 0).le_succ).ne
    -- The main subcase `f(a) = a + 1`
    rw [h4, or_iff_left (h3 _)] at h1
    have h5 : f (f (f (f 0 + 1))) = f (f 0 + 2) + 1 := h (f 0).succ
    have h6 : f (f (f (f (f 0 + 1)))) = f 0 + 5 := iter_four_eq_add_four h _
    rw [h5, h1, zero_add] at h6
    rw [h4, h1, zero_add] at h5
    rw [h5] at h1 h4 h6
    right; refine funext (add_four_induction h5 h6 h4 h1 ?_)
    intro n h7; rw [map_add_four h, h7, answer2]
  ---- Case 3: `a = a + 1`
  · exact absurd h5 a.lt_succ_self.ne

end Solution





/-- Final solution -/
theorem final_solution : good f ↔ f = Nat.succ ∨ f = answer2 :=
  ⟨good_imp_succ_or_answer2,
  λ h ↦ h.elim (λ h ↦ h.symm ▸ good_succ) (λ h ↦ h.symm ▸ good_answer2)⟩
