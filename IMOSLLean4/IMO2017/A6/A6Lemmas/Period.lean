/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Defs
import Mathlib.RingTheory.Congruence.Basic

/-!
# IMO 2017 A6 (P2, Periodic elements)

Let `f : R → R` be a good function and `I = {c : R | f(x + c) = f(x)}`.
Then `I` is a double-sided ideal, and the induced function `R/I → R/I` is reduced good.

### Implementation details

Instead of using ideals explicitly, we use the `RingCon` API.
The `RingCon` relation is implemented as `good.toRingCon`.
-/

namespace IMOSL
namespace IMO2017A6
namespace good

/-- The equivalence relation representing the set `I`, as an `AddCon`. -/
def PeriodEquiv [NonUnitalNonAssocSemiring R] (f : R → R) : AddCon R where
  r := λ c d ↦ ∀ x, f (x + c) = f (x + d)
  iseqv := ⟨λ _ _ ↦ rfl, λ h x ↦ (h x).symm, λ h h0 x ↦ (h x).trans (h0 x)⟩
  add' := λ h h0 x ↦ by rw [← add_assoc, h0, add_right_comm, h, add_right_comm, add_assoc]

lemma PeriodEquiv_map_eq [NonUnitalNonAssocSemiring R] {f : R → R} (h : PeriodEquiv f c d) :
    f c = f d := by
  rw [← zero_add c, h, zero_add]


section

variable [NonUnitalSemiring R] [IsCancelAdd R] {f : R → R} (hf : good f)
include hf

lemma PeriodEquiv_mul_left (h : PeriodEquiv f c d) : ∀ x, PeriodEquiv f (x * c) (x * d) :=
  have h0 (x) : f (x * c) = f (x * d) := by rw [← hf, ← hf x, PeriodEquiv_map_eq h, h]
  λ t x ↦ by rw [← add_right_inj, hf, h0, ← mul_assoc, h0, hf, mul_assoc]

lemma PeriodEquiv_mul_right (h : PeriodEquiv f c d) : ∀ x, PeriodEquiv f (c * x) (d * x) :=
  have h0 (x) : f (c * x) = f (d * x) := by
    rw [← hf, PeriodEquiv_map_eq h, add_comm c, h, add_comm x, hf]
  λ t x ↦ by rw [add_comm, ← add_right_inj, hf, h0, mul_assoc, h0, add_comm x, hf, mul_assoc]

lemma PeriodEquiv_mul (h : PeriodEquiv f c d) (h0 : PeriodEquiv f x y) :
    PeriodEquiv f (c * x) (d * y) :=
  (PeriodEquiv f).trans (PeriodEquiv_mul_right hf h x) (PeriodEquiv_mul_left hf h0 d)

lemma PeriodEquiv_map (h : PeriodEquiv f (f x) (f y)) : f x = f y := by
  have h0 := (hf.map_map_zero_mul_map x).trans (hf.map_map_zero_mul_map y).symm
  rwa [PeriodEquiv_map_eq (hf.PeriodEquiv_mul_left h (f 0)), add_right_inj] at h0


def toRingCon : RingCon R :=
  { PeriodEquiv f with mul' := λ h ↦ PeriodEquiv_mul hf h }

lemma toRingCon_rel_iff {c d} : hf.toRingCon c d ↔ PeriodEquiv f c d := Iff.rfl

lemma apply_eq_of_toRingCon_rel (h : hf.toRingCon c d) : f c = f d :=
  PeriodEquiv_map_eq h

lemma apply_eq_of_toRingQuot_eq {c d : R} (h : (c : hf.toRingCon.Quotient) = d) : f c = f d :=
  hf.apply_eq_of_toRingCon_rel ((RingCon.eq hf.toRingCon).mp h)





/-! ### The induced quotient map -/

/-- "Partial" quotient map `R/I → R` -/
def toPartialQuotientMap : hf.toRingCon.Quotient → R :=
  Quotient.lift f λ _ _ ↦ PeriodEquiv_map_eq

/-- The true quotient map `R/I → R/I` -/
def toQuotientMap : hf.toRingCon.Quotient → hf.toRingCon.Quotient :=
  λ x ↦ hf.toPartialQuotientMap x

lemma toQuotientMap_apply_mk (x : R) : hf.toQuotientMap x = f x := rfl

lemma toQuotientMap_good : good hf.toQuotientMap :=
  Quotient.ind₂ λ a b ↦ congrArg (Quotient.mk _) (hf a b)

lemma toQuotientMap_ReducedGood : ReducedGood hf.toQuotientMap :=
  ⟨hf.toQuotientMap_good, Quotient.ind₂ λ _ _ h ↦
    Quot.sound λ x ↦ hf.PeriodEquiv_map ((RingCon.eq hf.toRingCon).mp (h x))⟩

end


/-- `f` factors out through a ring homomorphism and the induced map. -/
lemma toQuotientMap_factor {R} [Semiring R] [IsCancelAdd R] {f : R → R} (hf : good f) :
    hf.toRingCon.mk' ∘ f = hf.toQuotientMap ∘ hf.toRingCon.mk' := rfl
