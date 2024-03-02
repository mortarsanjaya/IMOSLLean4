/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.A3Defs
import Mathlib.Data.Sigma.Basic

/-!
# IMO 2017 A3 (Direct sums)

We prove that if the direct sum of self-maps is good, then each
  component is good, in both binary sum and sigma version.
-/

namespace IMOSL
namespace IMO2017A3

open Function

/-! ### Binary sum -/

lemma bad_pair_sum_SelfMap {X Y : SelfMap} {g₁ : X.α → X.α} {g₂ : Y.α → Y.α}
    (h : bad_pair X.f g₁) (h0 : bad_pair Y.f g₂) :
    bad_pair (X.sum Y).f (Sum.map g₁ g₂) :=
  funext λ x ↦ match x with
    | Sum.inl a => congr_arg Sum.inl (congr_fun h a)
    | Sum.inr b => congr_arg Sum.inr (congr_fun h0 b)

theorem good_sum_inl {X Y : SelfMap} (h : good (X.sum Y)) : good X :=
  λ g h0 ↦ funext λ a ↦ Sum.inl.inj <|
    congr_fun (h (Sum.map g Y.f) (bad_pair_sum_SelfMap h0 rfl)) (Sum.inl a)

theorem good_sum_inr {X Y : SelfMap} (h : good (X.sum Y)) : good Y :=
  λ g h0 ↦ funext λ b ↦ Sum.inr.inj <|
    congr_fun (h (Sum.map X.f g) (bad_pair_sum_SelfMap rfl h0)) (Sum.inr b)



/-! ### Sigma -/

lemma bad_pair_sigma {α : I → Type*} {F G : (i : I) → α i → α i}
    (h : ∀ i, bad_pair (F i) (G i)) :
    bad_pair (Sigma.map id F) (Sigma.map id G) :=
  funext λ ⟨i, x⟩ ↦ Sigma.ext rfl <| heq_of_eq (congr_fun (h i) x)

theorem good_sigma_imp [DecidableEq I] {X : I → SelfMap}
    (h : good (SelfMap.sigma X)) (i) : good (X i) := λ g h0 ↦
  let F (i : I) : (X i).α → (X i).α := (X i).f
  have h1 : g = update F i g i := (update_same i g F).symm
  suffices ∀ j, bad_pair (X j).f (update F i g j)
    from funext λ a ↦ (congr_fun h1 a).trans <| eq_of_heq
      (Sigma.ext_iff.mp <| congr_fun (h _ (bad_pair_sigma this)) ⟨i, a⟩).2
  λ j ↦ (eq_or_ne j i).elim (λ h2 ↦ h2.symm ▸ h1 ▸ h0)
    (λ h2 ↦ update_noteq h2 _ _ ▸ rfl)
