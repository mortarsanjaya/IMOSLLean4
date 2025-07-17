/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Positive.Ring

/-!
# IMO 2007 A4

Let $G$ be a totally ordered abelian group and $G_{>0} = \{x ∈ G : x > 0\}$.
Find all functions $f : G_{>0} → G_{>0}$ such that for any $x, y ∈ G_{>0}$,
$$ f(x + f(y)) = f(x + y) + f(y). $$
-/

namespace IMOSL
namespace IMO2007A4

/-! ### Unbundled version of the problem -/

structure weakGood [AddCommMonoid M] [LinearOrder M] (f : M → M) : Prop where
  map_pos_of_pos : ∀ x, 0 < x → 0 < f x
  good' : ∀ x y, 0 < x → 0 < y → f (x + f y) = f (x + y) + f y

/-- Solution for the unboundled version -/
theorem weakGood_iff_add_self [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    {f : G → G} : weakGood f ↔ ∀ x, 0 < x → f x = x + x := by
  refine ⟨λ hf ↦ ?_, λ hf ↦ ?_⟩
  ---- `→` direction
  · rcases hf with ⟨hf, hf₀⟩
    obtain ⟨g, rfl⟩ : ∃ g : G → G, f = λ x ↦ g x + x :=
      ⟨λ x ↦ f x - x, funext λ x ↦ (sub_add_cancel (f x) x).symm⟩
    simp only at hf hf₀ ⊢
    replace hf {x} (hx : 0 < x) : 0 < g x := by
      apply (lt_trichotomy 0 (g x)).resolve_right; rintro (h | h)
      · specialize hf₀ x x hx hx
        rw [← h, zero_add, left_eq_add] at hf₀
        exact hx.ne hf₀.symm
      · rw [← neg_pos] at h
        specialize hf₀ (-g x) x h hx
        rw [neg_add_cancel_left, right_eq_add] at hf₀
        exact hf₀.not_gt (hf _ (add_pos h hx))
    replace hf₀ {t y} (h : 0 < y) (h0 : y < t) : g (t + g y) = g t + y := by
      specialize hf₀ (t - y) y (sub_pos_of_lt h0) h
      rwa [sub_add_add_cancel, sub_add_cancel, add_comm _ y,
        add_add_add_comm, add_left_inj] at hf₀
    have hg₁ {x y} (hx : 0 < x) (hy : 0 < y) (h : g x = g y) : x = y := by
      have h0 := hf₀ hy (lt_add_of_pos_left y hx)
      rwa [← h, hf₀ hx (lt_add_of_pos_right x hy), add_right_inj] at h0
    replace hg₁ {x y} (hx : 0 < x) (hy : 0 < y) : g (x + y) = g x + g y := by
      have h : 0 < x + y := add_pos hx hy
      obtain ⟨t, h0⟩ : ∃ t, x + y < t := ⟨x + y + x, lt_add_of_pos_right _ hx⟩
      have h1 : 0 < t := h.trans h0
      have hgx : 0 < g x := hf hx
      refine add_left_cancel (a := t)
        (hg₁ (add_pos h1 (hf h)) (add_pos h1 (add_pos hgx (hf hy))) ?_)
      have h2 := lt_add_of_lt_of_pos (lt_of_add_lt_of_nonneg_right h0 hx.le) hgx
      have h3 := lt_of_add_lt_of_nonneg_left h0 hy.le
      rw [hf₀ h h0, ← add_assoc, ← add_assoc, hf₀ hy h2, hf₀ hx h3]
    replace hf₀ {y} (hy : 0 < y) : g (g y) = y := by
      have h : y < y + y := lt_add_of_pos_left y hy
      rw [← add_right_inj, ← hg₁ (hy.trans h) (hf hy), hf₀ hy h]
    replace hg₁ {x y} (h : 0 < x) (h0 : x < y) : g x < g y := by
      rw [← sub_pos] at h0
      rw [← add_sub_cancel x y, hg₁ h h0, lt_add_iff_pos_right]
      exact hf h0
    -- Finishing; first resolve `g(x) < x`, then resolve `g(x) > x`.
    intro x hx; rw [add_left_inj]
    exact ((lt_trichotomy (g x) x).resolve_left
      λ h ↦ (hf₀ hx).not_lt (h.trans' (hg₁ (hf hx) h))).resolve_right
      λ h ↦ (hf₀ hx).not_gt (h.trans (hg₁ hx h))
  ---- `←` direction
  · refine ⟨λ x hx ↦ hf x hx ▸ add_pos hx hx, λ x y hx hy ↦ ?_⟩
    rw [hf y hy, hf _ (add_pos hx hy), add_add_add_comm x, add_assoc,
      add_add_add_comm x x, hf _ (add_pos hx (add_pos hy hy))]





/-! ### The main version -/

def posSubtypeExt [AddCommMonoid G] [LinearOrder G]
    (f : {x : G // 0 < x} → {x : G // 0 < x}) (x : G) : G :=
  dite (0 < x) (λ h ↦ f ⟨x, h⟩) (λ _ ↦ 0)

lemma posSubtypeExt_spec [AddCommMonoid G] [LinearOrder G]
    (f : {x : G // 0 < x} → {x : G // 0 < x}) (x : {x : G // 0 < x}) :
    posSubtypeExt f x.1 = f x :=
  dif_pos _

def good [Add G] (f : G → G) := ∀ x y, f (x + f y) = f (x + y) + f y

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

lemma good_iff_posSubtypeExt_weakGood {f : {x : G // 0 < x} → {x : G // 0 < x}} :
    good f ↔ weakGood (posSubtypeExt f) := by
  refine ⟨λ h ↦ ?_, ?_⟩
  · refine ⟨λ x hx ↦ (f ⟨x, hx⟩).2.trans_eq (posSubtypeExt_spec f _).symm, λ x y hx hy ↦ ?_⟩
    lift x to {x : G // 0 < x} using hx
    lift y to {x : G // 0 < x} using hy
    simp only [posSubtypeExt_spec, ← Positive.coe_add]
    exact congrArg _ (h x y)
  · rintro ⟨_, h0⟩ x y
    specialize h0 x.1 y.1 x.2 y.2
    simp only [posSubtypeExt_spec, ← Positive.coe_add] at h0
    exact Subtype.coe_inj.mp h0

/-- Final solution -/
theorem final_solution {f : {x : G // 0 < x} → {x : G // 0 < x}} :
    good f ↔ f = λ x ↦ x + x := by
  rw [good_iff_posSubtypeExt_weakGood, weakGood_iff_add_self, funext_iff]
  exact ⟨λ h x ↦ Subtype.coe_inj.mp ((posSubtypeExt_spec _ _).symm.trans (h x.1 x.2)),
    λ h x hx ↦ (posSubtypeExt_spec f ⟨x, hx⟩).trans (congrArg _ (h ⟨x, hx⟩))⟩
