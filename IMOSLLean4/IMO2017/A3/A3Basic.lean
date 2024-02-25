/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.A3Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Equiv
import Mathlib.Tactic.Common

/-!
# IMO 2017 A3 (Basic results)

We prove some basic results, mainly relating good maps with
  several self-map constructions, mainly isomorphisms and cores.
* If `f` is good and `g` is a core of `f`, then `g` is good.
* If `f` and `g` are isomorphic, then `f` is good iff `g` is good.
* If `f ⊕ g` is good, both `f` and `g` are good.
-/

namespace IMOSL
namespace IMO2017A3

lemma bad_pair_of_core (C : SelfMap.Core f g) (h : bad_pair g g') :
    bad_pair f (C.ι ∘ g' ∘ C.φ) := funext λ x ↦ by
  simp only [Function.comp_apply]
  rw [← C.ι.Semiconj, C.φ.Semiconj, C.φ.Semiconj, C.is_inv]
  exact congr_arg _ (congr_fun h _)

lemma good_of_core (C : SelfMap.Core f g) (h : good f) : good g := λ g' h0 ↦ by
  change id ∘ g' ∘ id = g
  rw [← C.half_conj, ← C.φ_comp_ι]
  exact congr_arg (λ s ↦ C.φ ∘ s ∘ C.ι) (h _ (bad_pair_of_core C h0))

lemma good_of_equiv (e : SelfMap.Equiv f g) (h : good f) : good g :=
  good_of_core e.toCore h

lemma good_iff_equiv (e : SelfMap.Equiv f g) : good f ↔ good g :=
  ⟨good_of_equiv e, good_of_equiv e.symm⟩

lemma bad_pair_sum_inl (h : bad_pair f g) (s : α → α) :
    bad_pair (Sum.map f s) (Sum.map g s) :=
  funext λ x ↦ match x with
    | Sum.inl x => congr_arg Sum.inl (congr_fun h x)
    | Sum.inr _ => rfl

lemma bad_pair_sum_inr (h : bad_pair f g) (s : α → α) :
    bad_pair (Sum.map s f) (Sum.map s g) :=
  funext λ x ↦ match x with
    | Sum.inl _ => rfl
    | Sum.inr x => congr_arg Sum.inr (congr_fun h x)

lemma good_inl_of_sum (h : good (Sum.map f g)) : good f :=
  λ _ h0 ↦ funext λ x ↦ Sum.inl.inj <|
    congr_fun (h _ (bad_pair_sum_inl h0 g)) (Sum.inl x)

lemma good_inr_of_sum (h : good (Sum.map f g)) : good g :=
  λ _ h0 ↦ funext λ x ↦ Sum.inr.inj <|
    congr_fun (h _ (bad_pair_sum_inr h0 f)) (Sum.inr x)
