/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Group.Defs

/-!
# IMO 2017 A8

Let $G$ be a dense totally ordered abelian group.
Suppose that for any $x, y ∈ R$, if $f(x) + y < f(y) + x$, then $f(x) + y ≤ 0 ≤ f(y) + x$.
Prove that $f(x) + y ≤ f(y) + x$ for all $x ≥ y$.
-/

namespace IMOSL
namespace IMO2017A8

variable [AddCommGroup G] [LinearOrder G]

def good (f : G → G) := ∀ x y : G, f x + y < f y + x → f x + y ≤ 0 ∧ 0 ≤ f y + x

def good_alt (g : G → G) := ∀ x y : G, g x < g y → g x ≤ x + y ∧ x + y ≤ g y

variable [IsOrderedAddMonoid G]

theorem good_imp_good_alt {f : G → G} (hf : good f) : good_alt (λ x ↦ x - f x) := by
  intro x y h; rw [sub_lt_sub_iff, add_comm, add_comm y] at h
  refine (hf y x h).symm.imp (λ h0 ↦ ?_) (λ h0 ↦ ?_)
  · rwa [sub_le_iff_le_add', add_left_comm, le_add_iff_nonneg_right]
  · rwa [le_sub_iff_add_le', ← add_assoc, add_le_iff_nonpos_left]

theorem dense_good_alt_imp_Monotone [DenselyOrdered G] {g : G → G} (hf : good_alt g) :
    Monotone g := by
  ---- First prove the claim
  have hf0 {x y} (h : x < y) {z} (hzy : g y - y < z) (hzx : z < g x - x) :
      g z = g x ∨ g z = g y := by
    -- First resolve the case `g(z) ≤ g(y)`
    rcases lt_trichotomy (g z) (g y) with h1 | h1 | h1
    · exact absurd (lt_add_of_sub_right_lt hzy) (hf z y h1).2.not_gt
    · right; exact h1
    -- Next resolve the case `g(z) ≥ g(x)`
    rcases lt_trichotomy (g x) (g z) with h2 | h2 | h2
    · exact absurd (add_lt_of_lt_sub_left hzx) (hf x z h2).1.not_gt
    · left; exact h2.symm
    -- Finally, resolve the case `g(y) < g(z) < g(x)`
    refine absurd ?_ ((hf y z h1).2.trans (hf z x h2).1).not_gt
    rwa [add_comm, add_lt_add_iff_right]
  ---- Reduce to the case `x < y`
  intro x y; rw [le_iff_eq_or_lt]
  rintro (rfl | h)
  · exact le_refl (g _)
  refine le_of_not_gt λ h0 ↦ ?_
  ---- Find `z` such that `x < z < y` and show that `g(z) ∈ {g(x), g(y)}`
  obtain ⟨z, hxz, hzy⟩ : ∃ z, x < z ∧ z < y := exists_between h
  obtain h1 | h1 : g z = g x ∨ g z = g y := by
    obtain ⟨h1, h2⟩ : g y ≤ y + x ∧ y + x ≤ g x := hf y x h0
    exact hf0 h (hxz.trans_le' (sub_left_le_of_le_add h1))
      (hzy.trans_le (le_tsub_of_add_le_right h2))
  ---- Case 1: `g(z) = g(x)`
  · -- Pick some `w ∈ G` such that `x < w < z`, then show `g(g(x) - w) ∈ {g(x), g(y)}`
    obtain ⟨w, hxw, hwz⟩ : ∃ w, x < w ∧ w < z := exists_between hxz
    obtain h2 | h2 : g (g x - w) = g x ∨ g (g x - w) = g y :=
      hf0 h (sub_lt_sub h0 (hwz.trans hzy)) (sub_lt_sub_left hxw _)
    -- Case 1.1: `g(g(x) - w) = g(x)`
    · have h3 : y + (g x - w) ≤ g (g x - w) := (hf _ _ (h0.trans_eq h2.symm)).2
      rw [h2, add_sub_left_comm, add_le_iff_nonpos_right, sub_nonpos] at h3
      exact h3.not_gt (hwz.trans hzy)
    -- Case 1.2: `g(g(x) - w) = g(y)`
    · have h3 : g x - w + z ≤ g z := (hf _ _ (h2.trans_lt (h0.trans_eq h1.symm))).2
      rw [h1, ← le_sub_iff_add_le, sub_le_sub_iff_left] at h3
      exact h3.not_gt hwz
  ---- Case 2: `g(z) = g(y)`
  · obtain ⟨w, hzw, hwy⟩ : ∃ w, z < w ∧ w < y := exists_between hzy
    obtain h2 | h2 : g (g y - w) = g x ∨ g (g y - w) = g y :=
      hf0 h (sub_lt_sub_left hwy _) (sub_lt_sub h0 (hxz.trans hzw))
    -- Case 2.1: `g(g(y) - w) = g(x)`
    · have h3 : g z ≤ z + (g y - w) := (hf _ _ (h1.trans_lt (h0.trans_eq h2.symm))).1
      rw [h1, add_sub_left_comm, le_add_iff_nonneg_right, sub_nonneg] at h3
      exact h3.not_gt hzw
    -- Case 2.2: `g(g(y) - w) = g(y)`
    · have h3 : g (g y - w) ≤ g y - w + x := (hf _ _ (h2.trans_lt h0)).1
      rw [h2, ← sub_le_iff_le_add, sub_le_sub_iff_left] at h3
      exact h3.not_gt (hxz.trans hzw)

/-- Final solution -/
theorem final_solution [DenselyOrdered G] {f : G → G} (hf : good f) {x y} (h : x ≤ y) :
    f y + x ≤ f x + y := by
  replace hf := dense_good_alt_imp_Monotone (good_imp_good_alt hf) h
  rwa [sub_le_sub_iff, add_comm, add_comm y] at hf





/-! ### Extra part -/

theorem discrete_counterexample (h : ¬DenselyOrdered G) :
    ∃ f : G → G, ¬(∀ x y, x ≤ y → f y + x ≤ f x + y) ∧ good f := by
  ---- First get some minimal positive element `g`
  obtain ⟨g, hg, hg0⟩ : ∃ g : G, 0 < g ∧ ∀ x > 0, g ≤ x := by
    contrapose! h; refine ⟨λ x y h0 ↦ ?_⟩
    obtain ⟨b, hb, hb0⟩ := h (y - x) (sub_pos_of_lt h0)
    exact ⟨b + x, lt_add_of_pos_left x hb, lt_tsub_iff_right.mp hb0⟩
  replace hg0 {x y} : x < y ↔ x + g ≤ y :=
    ⟨λ h0 ↦ add_le_of_le_sub_left (hg0 _ (sub_pos_of_lt h0)),
    (lt_add_of_pos_right x hg).trans_le⟩
  ---- Construct the desired function `f` and prove that `f(g) > f(0) + g`
  let f := λ x ↦ if x = 0 then -g else if x = g then g else -x
  refine ⟨f, λ h1 ↦ ?_, λ x y ↦ ?_⟩
  · apply (h1 0 g hg.le).not_gt; dsimp only [f]
    rwa [if_pos rfl, neg_add_cancel, if_neg hg.ne.symm, if_pos rfl, add_zero]
  ---- Finally, prove that `f` is good
  simp only [f]; split_ifs
  -- Case 1: `x = 0` and `y = 0`
  · subst x y; intro h0
    exact absurd rfl h0.ne
  -- Case 2: `x = 0` and `y = g`
  · subst x y; rintro -
    exact ⟨(neg_add_cancel g).le, hg.le.trans_eq (add_zero g).symm⟩
  -- Case 3: `x = 0` and `y ∉ {0, g}`
  · subst x; intro h0
    rw [hg0, add_zero, neg_add_cancel_comm, le_neg_self_iff] at h0
    refine ⟨add_nonpos (neg_nonpos.mpr hg.le) h0, ?_⟩
    rwa [add_zero, neg_nonneg]
  -- Case 4: `x = g` and `y = 0`
  · subst x y; intro h0
    refine absurd ?_ h0.not_gt
    rwa [neg_add_cancel, add_zero]
  -- Case 5: `x = g` and `y = g`
  · subst x y; intro h0
    exact absurd rfl h0.ne
  -- Case 6: `x = g` and `y ∉ {0, g}`
  · subst x; intro h0
    rw [add_comm, add_lt_add_iff_right, lt_neg_self_iff] at h0
    exact ⟨(add_comm g y).trans_le (hg0.mp h0), add_nonneg (neg_nonneg.mpr h0.le) hg.le⟩
  -- Case 7: `x ∉ {0, g}` and `y = 0`
  · subst y; intro h0
    rw [add_zero, hg0, neg_add_eq_sub, ← neg_sub, ← neg_add_eq_sub, neg_le_self_iff] at h0
    refine ⟨le_of_lt ?_, h0⟩
    rwa [add_zero, neg_lt_zero, hg0, zero_add, ← le_neg_add_iff_le]
  -- Case 8: `x ∉ {0, g}` and `y = g`
  · subst y; intro h0
    rw [add_comm, add_lt_add_iff_left, neg_lt_self_iff] at h0
    refine ⟨?_, (add_pos hg h0).le⟩
    rwa [neg_add_nonpos_iff, ← zero_add g, ← hg0]
  -- Case 9: `x ∉ {0, g}` and `y ∉ {0, g}`
  · intro h0; rw [neg_add_eq_sub, ← neg_sub, ← neg_add_eq_sub] at h0 ⊢
    rw [neg_nonpos, and_self]; exact (neg_lt_self_iff.mp h0).le

/-- Final solution, extra -/
theorem final_solution_extra :
    (∀ {f : G → G} (_ : good f) {x y}, x ≤ y → f y + x ≤ f x + y) ↔ DenselyOrdered G := by
  refine ⟨λ hG ↦ ?_, λ hG ↦ final_solution⟩
  contrapose! hG; obtain ⟨f, hf, hf0⟩ := discrete_counterexample hG
  simp only [not_forall, not_le] at hf
  rcases hf with ⟨x, y, h, h0⟩
  exact ⟨f, hf0, x, y, h, h0⟩
