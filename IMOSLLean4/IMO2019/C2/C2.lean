/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# IMO 2019 C2

Let $G$ be a totally ordered abelian group, and fix a non-negative element $g ∈ G$.
For a multiset $S$ of elements of $G$, let $Σ_S$ denote the
  sum of the elements of $S$, counting multiplicity.

Let $S$ be a multiset of non-negative elements of $G$ with $Σ_S ≤ 2|S| g$.
Suppose that each element of $S$ is greater than or equal to $g$.
Prove that, for any $r ∈ G$ with $-2g ≤ r ≤ Σ_S$, there exists
  a sub-multiset $S'$ of $S$ such that $r ≤ Σ_{S'} ≤ r + 2g$.
-/

namespace IMOSL
namespace IMO2019C2

open Multiset

variable [LinearOrder α]

theorem multiset_max_mem_cons (a : α) (S : Multiset α) : S.fold max a ∈ a ::ₘ S :=
  Multiset.induction_on S (mem_cons_self a 0) λ b T h ↦ by
    rw [fold_cons_left, cons_swap]
    rcases max_choice b (T.fold max a) with h0 | h0
    · rw [h0]; exact mem_cons_self b _
    · rw [h0]; exact mem_cons_of_mem h

theorem multiset_le_max_of_mem (a : α) (S : Multiset α) :
    ∀ b : α, b ∈ a ::ₘ S → b ≤ S.fold max a :=
  Multiset.induction_on S (λ _ h => (mem_singleton.mp h).le) λ b T h c h0 ↦ by
    rw [fold_cons_left, le_max_iff]
    rw [cons_swap, mem_cons] at h0
    exact h0.imp le_of_eq (h c)

theorem exists_max_add_rest {S : Multiset α} (h : S ≠ 0) :
    ∃ (a : α) (S₀ : Multiset α), S = a ::ₘ S₀ ∧ ∀ x : α, x ∈ S₀ → x ≤ a := by
  rcases exists_mem_of_ne_zero h with ⟨b, h0⟩
  rcases exists_cons_of_mem h0 with ⟨T, rfl⟩
  rcases exists_cons_of_mem (multiset_max_mem_cons b T) with ⟨U, h1⟩
  refine ⟨T.fold max b, U, h1, λ x h2 ↦ multiset_le_max_of_mem _ _ _ ?_⟩
  rw [h1]; exact mem_cons_of_mem h2

theorem LinearOrder_induction {P : Multiset α → Prop}
    (h : P 0) (h0 : ∀ a S, P S → (∀ x ∈ S, x ≤ a) → P (a ::ₘ S)) (S) : P S := by
  generalize hS : card S = n
  induction' n with n h1 generalizing S
  · exact card_eq_zero.mp hS ▸ h
  · obtain ⟨a, S₀, rfl, h2⟩ : ∃ a S₀, S = a ::ₘ S₀ ∧ ∀ x : α, x ∈ S₀ → x ≤ a :=
      exists_max_add_rest (card_pos.mp (n.succ_pos.trans_eq hS.symm))
    rw [card_cons, Nat.succ_inj] at hS
    exact h0 a S₀ (h1 S₀ hS) h2



/-- Final solution -/
theorem final_solution [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (g : G) :
    ∀ (S : Multiset G) (_ : ∀ x : G, x ∈ S → g ≤ x) (_ : S.sum ≤ (2 * card S) • g)
      {r : G} (_ : -(2 • g) ≤ r) (_ : r ≤ S.sum),
        ∃ T : Multiset G, T ≤ S ∧ r ≤ T.sum ∧ T.sum ≤ r + 2 • g :=
  LinearOrder_induction
    ---- Base case: `S = 0`
    (λ _ _ r hr hr0 ↦ ⟨0, le_refl _, hr0, neg_le_iff_add_nonneg.mp hr⟩)
    ---- Induction step
    λ s₀ S₀ h h0 h1 h2 ↦ by
      -- Step 1: Fill in the induction hypothesis for `S₀`
      rw [forall_mem_cons] at h1; rcases h1 with ⟨-, h1⟩
      rw [card_cons, Nat.mul_succ, sum_cons, add_nsmul, add_comm] at h2
      replace h (r) : -(2 • g) ≤ r → r ≤ S₀.sum → ∃ T ≤ S₀, r ≤ T.sum ∧ T.sum ≤ r + 2 • g := by
        refine h h1 (le_of_not_gt λ h3 ↦ h2.not_gt (add_lt_add h3 ?_))
        replace h3 := h3.trans_le (sum_le_card_nsmul S₀ s₀ h0)
        rw [mul_nsmul] at h3; exact lt_of_nsmul_lt_nsmul_right _ h3
      -- Step 2: Solve the problem, assuming `s₀ - 2g ≤ Σ_{S_0}`
      suffices s₀ + -(2 • g) ≤ S₀.sum by
        clear h0 h1 h2; intro r hr hr₀
        obtain (hr | hr₀) : s₀ + -(2 • g) ≤ r ∨ r ≤ S₀.sum := this.ge_or_le r
        · rw [sum_cons, ← sub_le_iff_le_add'] at hr₀
          specialize h (r - s₀) (le_sub_iff_add_le'.mpr hr) hr₀
          rcases h with ⟨T, h, h0, h1⟩
          refine ⟨s₀ ::ₘ T, (cons_le_cons_iff s₀).mpr h, ?_, ?_⟩
          · rwa [sum_cons, ← sub_le_iff_le_add']
          · rwa [sum_cons, ← le_sub_iff_add_le', add_sub_right_comm]
        · specialize h r hr hr₀; rcases h with ⟨T, h, h0⟩
          exact ⟨T, h.trans (le_cons_self S₀ s₀), h0⟩
      -- Step 3: Prove that `s_0 - 2g ≤ Σ_{S_0}`
      refine add_neg_le_iff_le_add.mpr (le_of_add_le_add_left (a := S₀.sum) (h2.trans ?_))
      rw [← add_assoc, add_le_add_iff_right, ← two_nsmul, mul_nsmul']
      exact nsmul_le_nsmul_right (card_nsmul_le_sum h1) 2
