/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6MainResults.TwoTorsionFree
import IMOSLLean4.IMO2017.A6.A6MainResults.Field
import IMOSLLean4.IMO2017.A6.A6RingCon
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Congruence.Basic

/-!
# IMO 2017 A6 (P2)

Let $R$ be a ring, $S$ be an abelian group, and $ι : R → S$ be a function.
Determine all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(ι(f(x)) ι(f(y))) + f(x + y) = f(xy). $$
-/

namespace IMOSL
namespace IMO2017A6

@[deprecated]
theorem good_iff_exists_nonperiodicGood_hom
    [Semiring R] [AddZeroClass S] [IsCancelAdd S] {ι : S →+ R} {f : R → S} :
    good ι f ↔ ∃ (rc : RingCon R) (g : rc.Quotient → S),
      nonperiodicGood (rc.mk'.toAddMonoidHom.comp ι) g ∧ f = g ∘ rc.toQuotient :=
  good_iff_exists_nonperiodicGood

theorem final_solution_TorsionFree23 [Ring R] [AddCommGroup S]
    (hS2 : ∀ x y : S, 2 • x = 2 • y → x = y)
    (hS3 : ∀ x y : S, 3 • x = 3 • y → x = y)
    (ι : S →+ R) {f : R → S} :
    good ι f ↔ ∃ (rc : RingCon R) (a : {a : rc.Quotient // a * a = 1 ∧ ∀ x, a * x = x * a})
      (φ : rc.Quotient →+ S), (∀ x, ι (φ x) = x) ∧ (∀ x, f x = φ (a * (1 - x))) := by
  rw [good_iff_exists_nonperiodicGood_hom]
  simp only [TwoThreeTorsionFree_nonperiodicGood_iff hS2 hS3]
  refine ⟨?_, ?_⟩
  · rintro ⟨rc, g, ⟨a, φ, h, rfl⟩, rfl⟩
    exact ⟨rc, a, φ, h, λ _ ↦ rfl⟩
  · rintro ⟨rc, a, φ, h, h0⟩
    exact ⟨rc, _, ⟨a, φ, h, rfl⟩, funext h0⟩

theorem DivisionRing_RingCon_eq_bot_or_top [DivisionRing R] (rc : RingCon R) :
    rc = ⊥ ∨ rc = ⊤ := by
  sorry
