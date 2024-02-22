/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.A3Equiv
import IMOSLLean4.IMO2017.A3.SelfMap.Hom.SplitMap
import Mathlib.Data.Sum.Basic

/-!
# IMO 2017 A3 (Good maps and splitting of core structures)

This file proves results relating core structures and good maps.
In particular, we prove the following results:
* If `f` is good and `g` is a core of `f`, then `g` is good.
* If `f` and `g` are equivalent, then `f` is good iff `g` is good.
* If `f : α → α` is good with core `g : β → β`, then
  `f` is isomorphic to `SplitMap g s` for some `s : β → α`.
Then we proceed to prove a necessary and sufficient condition
  for `SplitMap f s` to be a good map, when `f` is injective.
-/

namespace IMOSL
namespace IMO2017A3

open SelfMap Function

lemma good_core_splits (C : Core f g) (h : good f) : C.ι ∘ g ∘ C.φ = f :=
  h _ (bad_pair_of_core C rfl)

noncomputable def good_core_SplitMapEquiv (C : Core f g) (h : good f) :
    SelfMap.Equiv C.toSplitMap f :=
  C.toSplitMapEquiv (good_core_splits C h)

lemma good_core_exists_SplitMapEquiv
    {α : Type u} {f : α → α} {g : β → β} (C : Core f g) (h : good f) :
    ∃ (γ : Type u) (s : γ → β), Nonempty (SelfMap.Equiv (SplitMap g s) f) :=
  ⟨_, _, ⟨good_core_SplitMapEquiv C h⟩⟩





/-! ### Good split maps; necessary condition -/

lemma good_SplitMap_imp_core (h : good (SplitMap f s)) : good f :=
  good_of_core (SplitMap.toCore f s) h


section

open SplitMap

variable [DecidableEq α] [DecidableEq β]
  {f : α → α} {s : β → α} (h : good (SplitMap f s))

lemma good_SplitMap_imp1 (x y) : f (s x) ≠ s y := λ h0 ↦ by
  let g := update (SplitMap f s) (Sum.inr x) (Sum.inr y)
  refine absurd (h g ?_) (update_ne_self_iff.mpr Sum.inr_ne_inl)
  have h1 (z) : g (SplitMap f s z) = SplitMap f s (SplitMap f s z) :=
    update_noteq Sum.inl_ne_inr _ _
  funext z; iterate 4 rw [comp_apply]
  rw [h1, h1]; dsimp only [g]
  rcases ne_or_eq z (Sum.inr x) with h1 | rfl
  · rw [update_noteq h1]
  · rw [update_same, apply_inr, apply_inr, h0, apply_inl]

lemma good_SplitMap_imp2 (h0 : ∀ a', f a' ≠ a) (b) : s b ≠ f a := λ h1 ↦ by
  let g := update (SplitMap f s) (Sum.inl a) (Sum.inr b)
  refine absurd (h g ?_) (update_ne_self_iff.mpr Sum.inr_ne_inl)
  have h2 (z) : g (SplitMap f s z) = SplitMap f s (SplitMap f s z) :=
    update_noteq (λ h2 ↦ h0 _ (Sum.inl_injective h2)) _ _
  funext z; iterate 4 rw [comp_apply]
  rw [h2, h2]; dsimp only [g]
  rcases ne_or_eq z (Sum.inl a) with h2 | rfl
  · rw [update_noteq h2]
  · rw [update_same, apply_inl, apply_inr, h1, apply_inl]

lemma good_SplitMap_imp3 (h0 : ∀ a', f (f a') ≠ a) (b) : s b ≠ f a := λ h1 ↦ by
  let g := update (SplitMap f s) (Sum.inl a) (Sum.inr b)
  refine absurd (h g ?_) (update_ne_self_iff.mpr Sum.inr_ne_inl)
  have h2 (z) : SplitMap f s (g z) = SplitMap f s (SplitMap f s z) := by
    refine (ne_or_eq z (Sum.inl a)).elim
      (λ h2 ↦ congr_arg _ (update_noteq h2 _ _)) (λ h2 ↦ ?_)
    dsimp only [g]
    rw [h2, update_same, apply_inr, h1]; rfl
  funext z; iterate 4 rw [comp_apply]
  rw [h2, h2]
  exact (update_noteq (λ h2 ↦ h0 _ (Sum.inl_injective h2)) _ _).symm



/-- The three necessary condition for `SplitMap f s` to be good.
  It excludes the condition that `f` is good. -/
structure SplitMap_good_cond (f : α → α) (s : β → α) : Prop where
  cond1 : ∀ x y, f (s x) ≠ s y
  cond2 : ∀ a, (∀ a', f a' ≠ a) → ∀ b, s b ≠ f a
  cond3 : ∀ a, (∀ a', f (f a') ≠ a) → ∀ b, s b ≠ f a

lemma SplitMap_good_imp : SplitMap_good_cond f s where
  cond1 := good_SplitMap_imp1 h
  cond2 := λ _ ↦ good_SplitMap_imp2 h
  cond3 := λ _ ↦ good_SplitMap_imp3 h

end





/-! ### Good split maps; sufficient and iff condition -/

lemma SplitMap_good_of_cond
    (h : Injective f) (h0 : good f) (h1 : SplitMap_good_cond f s) :
    good (SplitMap f s) := λ g h2 ↦ by
  replace h0 : ∀ a, Sum.elim id s (g (Sum.inl a)) = f a :=
    congr_fun <| h0 _ <| funext λ a ↦
      congr_arg (Sum.elim id s) (congr_fun h2 (Sum.inl a))
  replace h2 (z) : Sum.inl (f (f (f (Sum.elim id s z))))
      = g (Sum.inl (f (Sum.elim id s (g z)))) := by
    rw [← h0 (f (Sum.elim id s z))]; exact congr_fun h2 z
  funext z
  have h3 : f (Sum.elim id s z) = Sum.elim id s (g z) :=
    h <| h <| by rw [← h0 (f (Sum.elim id s (g z))), ← h2]; rfl
  rw [SplitMap, comp_apply, comp_apply, h3]
  cases h4 : g z with | inl a => rfl | inr b =>
    rw [h4, Sum.elim_inr] at h3
    exfalso; cases z with | inr b' => exact h1.cond1 b' b h3 | inl a =>
      rcases (em' (∃ a', f a' = a)) with h4 | ⟨a', rfl⟩
      · exact h1.cond2 _ (not_exists.mp h4) b h3.symm
      rcases (em' (∃ a, f a = a')) with h4 | ⟨a, rfl⟩
      · exact h1.cond3 (f a') (λ a h5 ↦ h4 ⟨a, h h5⟩) b h3.symm
      · specialize h2 (Sum.inl a)
        rw [h0, h4] at h2
        exact Sum.inl_ne_inr h2

/-- `SplitMap_good_cond f s` plus `good f` is
  necessary and sufficient for `SelfMap f s` to be good. -/
theorem SplitMap_good_iff [DecidableEq α] [DecidableEq β]
    {f : α → α} (h : Injective f) {s : β → α} :
    good (SplitMap f s) ↔ (good f ∧ SplitMap_good_cond f s) :=
  ⟨λ h ↦ ⟨good_SplitMap_imp_core h, SplitMap_good_imp h⟩,
  λ h0 ↦ SplitMap_good_of_cond h h0.1 h0.2⟩
