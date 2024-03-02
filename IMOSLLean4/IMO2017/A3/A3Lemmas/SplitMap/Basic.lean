/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.A3Lemmas.Core
import IMOSLLean4.IMO2017.A3.SelfMap.Core.Split
import IMOSLLean4.IMO2017.A3.SelfMap.SplitMap.Core

/-!
# IMO 2017 A3 (Good maps and splitting of core structures)

This file proves results relating core structures and good maps.
We prove a nice characterization of good split maps, and we prove when
  the sum of two split maps is a good map in terms of the components.
-/

namespace IMOSL
namespace IMO2017A3

open SelfMap Function

lemma good_core_splits (C : Core X Y) (h : good X) : C.splits :=
  h _ (bad_pair_of_core C rfl)

lemma good_core_exists_SplitMapEquiv
    {X : SelfMap.{u}} (C : Core X Y) (h : good X) :
    ∃ (β : Type u) (s : β → Y.α), Nonempty ((SplitMap Y s).Equiv X) :=
  C.Nonempty_SplitMapEquiv_of_splits (good_core_splits C h)





/-! ### Good split maps; necessary condition -/

lemma good_SplitMap_imp_core (h : good (SplitMap X s)) : good X :=
  good_of_core (SplitMap.toCore X s) h


section

open SplitMap
open scoped Classical

variable (h : good (SplitMap X s))

lemma good_SplitMap_imp1 (x y) : X.f (s x) ≠ s y := λ h0 ↦ by
  let fY := (SplitMap X s).f
  let g := update fY (Sum.inr x) (Sum.inr y)
  refine absurd (h g ?_) (update_ne_self_iff.mpr Sum.inr_ne_inl)
  have h1 (z) : g (fY z) = fY (fY z) :=
    update_noteq (a := fY z) Sum.inl_ne_inr _ _
  funext z; iterate 4 rw [comp_apply]
  rw [h1, h1]; dsimp only [g]
  rcases ne_or_eq z (Sum.inr x) with h1 | rfl
  · rw [update_noteq h1]
  · rw [update_same, apply_inr, apply_inr, h0, apply_inl]

lemma good_SplitMap_imp2 (h0 : ∀ a', X.f a' ≠ a) (b) : s b ≠ X.f a := λ h1 ↦ by
  let fY := (SplitMap X s).f
  let g := update fY (Sum.inl a) (Sum.inr b)
  refine absurd (h g ?_) (update_ne_self_iff.mpr Sum.inr_ne_inl)
  have h2 (z) : g (fY z) = fY (fY z) :=
    update_noteq (a := fY z) (λ h2 ↦ h0 _ (Sum.inl.inj h2)) _ _
  funext z; iterate 4 rw [comp_apply]
  rw [h2, h2]; dsimp only [g]
  rcases ne_or_eq z (Sum.inl a) with h2 | rfl
  · rw [update_noteq h2]
  · rw [update_same, apply_inl, apply_inr, h1, apply_inl]

lemma good_SplitMap_imp3 (h0 : ∀ a', X.f (X.f a') ≠ a) (b) :
    s b ≠ X.f a := λ h1 ↦ by
  let fY := (SplitMap X s).f
  let g := update fY (Sum.inl a) (Sum.inr b)
  refine absurd (h g ?_) (update_ne_self_iff.mpr Sum.inr_ne_inl)
  have h2 (z) : fY (g z) = fY (fY z) := by
    refine (eq_or_ne z (Sum.inl a)).elim (λ h2 ↦ ?_)
      (λ h2 ↦ congr_arg _ (update_noteq h2 _ _))
    dsimp only [g]; rw [h2, update_same, apply_inr, h1]; rfl
  funext z; change fY (g (fY z)) = g (fY (g z))
  rw [h2, h2]
  exact (update_noteq (a := fY (fY z)) (λ h2 ↦ h0 _ (Sum.inl.inj h2)) _ _).symm



/-- The three necessary condition for `SplitMap X s` to be good.
  It excludes the condition that `X` is good. -/
structure SplitMap_good_cond (X : SelfMap) (s : β → X.α) : Prop where
  cond1 : ∀ x y, X.f (s x) ≠ s y
  cond2 : ∀ a, (∀ a', X.f a' ≠ a) → ∀ b, s b ≠ X.f a
  cond3 : ∀ a, (∀ a', X.f (X.f a') ≠ a) → ∀ b, s b ≠ X.f a

lemma SplitMap_good_imp : SplitMap_good_cond X s where
  cond1 := good_SplitMap_imp1 h
  cond2 := λ _ ↦ good_SplitMap_imp2 h
  cond3 := λ _ ↦ good_SplitMap_imp3 h

end





/-! ### Good split maps; sufficient and iff condition -/

lemma SplitMap_good_of_cond {X : SelfMap} {s : β → X.α}
    (h : good X) (h0 : Injective X.f) (h1 : SplitMap_good_cond X s) :
    good (SplitMap X s) := λ g h2 ↦ by
  let φ := SplitMap_sum_proj X s
  replace h : ∀ a, φ (g (Sum.inl a)) = X.f a :=
    congr_fun <| h _ <| funext λ a ↦ congr_arg φ (congr_fun h2 (Sum.inl a))
  replace h2 (z) : Sum.inl (X.f (X.f (X.f (φ z))))
      = g (Sum.inl (X.f (φ (g z)))) := by
    rw [← h (X.f (φ z))]; exact congr_fun h2 z
  funext z
  have h3 : X.f (φ z) = φ (g z) :=
    h0 <| h0 <| by rw [← h (X.f (φ (g z))), ← h2]
  rw [SplitMap.apply, h3]
  cases h4 : g z with | inl a => rfl | inr b =>
    exfalso; rw [h4] at h3
    cases z with | inr b' => exact h1.cond1 b' b h3 | inl a =>
      rcases (em' (∃ a', X.f a' = a)) with h4 | ⟨a', rfl⟩
      · exact h1.cond2 _ (not_exists.mp h4) b h3.symm
      rcases (em' (∃ a, X.f a = a')) with h4 | ⟨a, rfl⟩
      · exact h1.cond3 (X.f a') (λ a h5 ↦ h4 ⟨a, h0 h5⟩) b h3.symm
      · specialize h2 (Sum.inl a)
        rw [h, h4] at h2
        exact Sum.inl_ne_inr h2

/-- Assuming that `X` is good, `SplitMap X s` is good iff
  the condition `SplitMap_good_cond X s` holds. -/
theorem SplitMap_good_iff (h : good X) (h0 : Injective X.f) {s : β → X.α}:
    good (SplitMap X s) ↔ SplitMap_good_cond X s :=
  ⟨SplitMap_good_imp, SplitMap_good_of_cond h h0⟩
