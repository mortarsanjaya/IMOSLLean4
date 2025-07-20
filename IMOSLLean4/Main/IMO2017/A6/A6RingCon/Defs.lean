/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2017.A6.A6Defs
import Mathlib.RingTheory.Congruence.Defs

/-!
# IMO 2017 A6 (P2, Ring congruence: general to non-periodic)

Let $I$ be a double-sided ideal of $R$, and let $φ : R → R/I$ be the projection map.
Then any $φι$-good function $f : R/I → G$ lifts to an $ι$-good function $f ∘ φ$.

Conversely, let $f : R → G$ be an $ι$-good function.
The set $I_f$ of periods of $f$ form a double-sided ideal of $R$.
The induced function $\tilde{f} : R/I → G$ is non-periodic $φι$-good function,
  where $φ$ is the projection map from $R$ to $R/I$.
Thus we get a correspondence between good functions and non-periodic good functions.

### Implementation notes

Instead of using ideals explicitly, we use the `RingCon` API.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### General period congruence -/

/-- General additive congruence induced by period. -/
def PeriodEquiv [AddCommSemigroup R] (f : R → α) : AddCon R where
  r c d := ∀ x, f (x + c) = f (x + d)
  iseqv := ⟨λ _ _ ↦ rfl, λ h x ↦ (h x).symm, λ h h0 x ↦ (h x).trans (h0 x)⟩
  add' h h0 x := by rw [← add_assoc, h0, add_right_comm, h, add_right_comm, add_assoc]

lemma PeriodEquiv_map_eq [AddCommMonoid R] {f : R → α} (h : PeriodEquiv f c d) :
    f c = f d := by
  simpa only [zero_add] using h 0





/-! ### Period ring congruence induced by good functions -/

section

variable [AddCommMonoid R] [Semigroup R] [Add G] [IsCancelAdd G] {ι : G → R}

namespace GoodFun

/-- The ring congruence induced by an `ι`-good map. -/
def inducedRingCon (f : GoodFun ι) : RingCon R :=
  { PeriodEquiv f with
    mul' := by
      intro a b c d h h0 x
      have X {c d} (h1 : ∀ x, f (x + c) = f (x + d)) : f c = f d := PeriodEquiv_map_eq h1
      have h1 := map_mul_eq_of_map_eq_of_map_add_eq ι
        (X h) (X h0) (X ((PeriodEquiv f).add' h h0))
      rw [map_add_left_eq_iff_map_mul_left_eq ι h1, ← mul_assoc, ← mul_assoc]
      replace h1 (x) : f (x * a) = f (x * b) :=
        map_mul_left_eq_of_map_add_left_eq ι (X h) (h x)
      refine map_mul_eq_of_map_eq_of_map_add_eq ι (h1 x) (X h0) ?_
      rw [h0, add_comm, add_comm _ d, map_add_left_eq_iff_map_mul_left_eq ι (h1 x)]
      simpa only [mul_assoc] using h1 (d * x) }

/-- Definition of congruence relation given by `inducedRingCon`. -/
theorem inducedRingCon_def {f : GoodFun ι} :
    f.inducedRingCon c d ↔ ∀ x, f (x + c) = f (x + d) := Iff.rfl

theorem inducedRingConEquiv_map_eq {f : GoodFun ι} (h : inducedRingCon f c d) : f c = f d :=
  PeriodEquiv_map_eq h

/-- The induced non-periodic good quotient map. -/
def Quotient (f : GoodFun ι) : NonperiodicGoodFun (f.inducedRingCon.toQuotient ∘ ι) where
  toFun := Quotient.lift f λ _ _ ↦ inducedRingConEquiv_map_eq
  good_def' := Quotient.ind₂ (good_def ι f)
  period_imp_eq' := Quotient.ind₂ λ _ _ h ↦ Quot.sound λ x ↦ h x

/-- Definition of the quotient map. -/
lemma Quotient_apply_mk (f : GoodFun ι) (x : R) : f.Quotient x = f x := rfl

end GoodFun


/-- Correspondence between good functions and non-periodic good functions. -/
theorem IsGoodFun_iff_Nonperiodic :
    IsGoodFun ι f ↔ ∃ (rc : RingCon R) (g : rc.Quotient → G),
      IsNonperiodicGoodFun (rc.toQuotient ∘ ι) g ∧ f = g ∘ rc.toQuotient :=
  ⟨λ h ↦ let f₀ := h.toGoodFun; let g := f₀.Quotient;
    ⟨f₀.inducedRingCon, g, g.IsNonperiodicGoodFun, rfl⟩,
  λ ⟨_, _, h, h0⟩ ↦ h0 ▸ ⟨λ x y ↦ h.good_def x y⟩⟩

end
