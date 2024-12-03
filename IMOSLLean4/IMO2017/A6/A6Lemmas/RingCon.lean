/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Defs
import Mathlib.RingTheory.Congruence.Basic

/-!
# IMO 2017 A6 (P2, Good functions and congruence with respect to periods)

Let `f : R → R` be a good function and `I = {c : R | f(x + c) = f(x)}`.
Then `I` is a double-sided ideal, and the induced function `R/I → R/I` is reduced good.
Conversely, a good function over `R/I` can be lifted to a
  good function over `R` by a group homomorphism `R/I → R`.

### Implementation details

Instead of using ideals explicitly, we use the `RingCon` API.
The `RingCon` relation is implemented as `good.toRingCon`.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Lift of good functions from quotient ring -/

def GoodFun.quotient_lift [NonUnitalNonAssocSemiring R]
    (rc : RingCon R) (ι : rc.Quotient →+ R) (h : Function.LeftInverse rc.toQuotient ι)
    (f : GoodFun rc.Quotient) : GoodFun R where
  toFun := λ x ↦ ι (f x)
  good_def' := λ x y ↦ by
    simp only [rc.coe_mul]; rw [h, h, rc.coe_add, ← ι.map_add, good_def]





/-! ### Congruence induced by periods -/

/-- The equivalence relation representing the set `I`, as an `AddCon`. -/
def PeriodEquiv [NonUnitalNonAssocSemiring R] (f : R → R) : AddCon R where
  r := λ c d ↦ ∀ x, f (x + c) = f (x + d)
  iseqv := ⟨λ _ _ ↦ rfl, λ h x ↦ (h x).symm, λ h h0 x ↦ (h x).trans (h0 x)⟩
  add' := λ h h0 x ↦ by rw [← add_assoc, h0, add_right_comm, h, add_right_comm, add_assoc]

lemma PeriodEquiv_map_eq [NonUnitalNonAssocSemiring R]
    {f : R → R} (h : PeriodEquiv f c d) : f c = f d := by
  rw [← zero_add c, h, zero_add]


section

variable [NonUnitalSemiring R] [IsCancelAdd R] [FunLike F R R] [GoodFunClass F R] (f : F)

lemma PeriodEquiv_mul_left (h : PeriodEquiv f c d) : ∀ x, PeriodEquiv f (x * c) (x * d) :=
  have h0 (x) : f (x * c) = f (x * d) := by
    rw [← good_def, ← good_def f x, PeriodEquiv_map_eq h, h]
  λ t x ↦ by rw [← add_right_inj, good_def, h0, ← mul_assoc, h0, good_def, mul_assoc]

lemma PeriodEquiv_mul_right (h : PeriodEquiv f c d) : ∀ x, PeriodEquiv f (c * x) (d * x) :=
  have h0 (x) : f (c * x) = f (d * x) := by
    rw [← good_def, PeriodEquiv_map_eq h, add_comm c, h, add_comm x, good_def]
  λ t x ↦ by rw [add_comm, ← add_right_inj, good_def, h0,
    mul_assoc, h0, add_comm x, good_def, mul_assoc]

lemma PeriodEquiv_mul (h : PeriodEquiv f c d) (h0 : PeriodEquiv f x y) :
    PeriodEquiv f (c * x) (d * y) :=
  (PeriodEquiv f).trans (PeriodEquiv_mul_right f h x) (PeriodEquiv_mul_left f h0 d)

lemma PeriodEquiv_map (h : PeriodEquiv f (f x) (f y)) : f x = f y := by
  have h0 := (map_map_zero_mul_map f x).trans (map_map_zero_mul_map f y).symm
  rwa [PeriodEquiv_map_eq (PeriodEquiv_mul_left f h (f 0)), add_right_inj] at h0


def toRingCon : RingCon R :=
  { PeriodEquiv f with mul' := λ h ↦ PeriodEquiv_mul f h }

lemma toRingCon_rel_iff {c d} : toRingCon f c d ↔ PeriodEquiv f c d := Iff.rfl

lemma apply_eq_of_toRingCon_rel (h : toRingCon f c d) : f c = f d :=
  PeriodEquiv_map_eq h

lemma apply_eq_of_toRingQuot_eq {c d : R} (h : (c : (toRingCon f).Quotient) = d) :
    f c = f d :=
  apply_eq_of_toRingCon_rel f ((toRingCon f).eq.mp h)





/-! ### The induced map on quotient rings -/

/-- "Partial" quotient map `R/I → R` -/
def toPartialQuotientMap : (toRingCon f).Quotient → R :=
  Quotient.lift f λ _ _ ↦ PeriodEquiv_map_eq

/-- The true quotient map `R/I → R/I` -/
def toQuotientMap : NonperiodicGoodFun (toRingCon f).Quotient where
  toFun := λ x ↦ toPartialQuotientMap f x
  good_def' := Quotient.ind₂ λ a b ↦ congrArg (Quotient.mk _) (good_def f a b)
  period_imp_eq' := Quotient.ind₂ λ _ _ h ↦
    Quot.sound λ x ↦ PeriodEquiv_map f ((toRingCon f).eq.mp (h x))

lemma toQuotientMap_apply_mk (x : R) : toQuotientMap f x = f x := rfl

end
