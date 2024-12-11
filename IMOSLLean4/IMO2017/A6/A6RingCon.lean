/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Defs
import Mathlib.RingTheory.Congruence.Defs

/-!
# IMO 2017 A6 (P2, Ring congruence: from general to non-periodic)

Let $I$ be a double-sided ideal of $R$, and let $φ : R → R/I$ be the projection map.
Then any $φι$-good function $f : R/I → S$ lifts to an $ι$-good function $f ∘ φ$.

Conversely, let $f : R → S$ be an $ι$-good function.
The set $I_f$ of periods of $f$ form a double-sided ideal of $R$.
The induced function $\tilde{f} : R/I → S$ is non-periodic $φι$-good function,
  where $φ$ is the projection map from $R$ to $R/I$.
Thus we get a correspondence between good functions and non-periodic good functions.

### Implementation notes

Instead of using ideals explicitly, we use the `RingCon` API.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Extension of good functions -/

namespace GoodFun

variable [Add R] [Mul R] [Add S] {ι : S → R} {rc : RingCon R}

/-- Extension of an `ι`-good function via the quotient map. -/
def Lift (f : GoodFun (rc.toQuotient ∘ ι)) : GoodFun ι where
  toFun x := f x
  good_def' x y := good_def (rc.toQuotient ∘ ι) f x y

theorem lift_def (f : GoodFun (rc.toQuotient ∘ ι)) (x) : f.Lift x = f x := rfl

end GoodFun





/-! ### Projecting down by period congruence -/

private def PeriodEquiv [AddCommSemigroup R] (f : R → S) : AddCon R where
  r := λ c d ↦ ∀ x, f (x + c) = f (x + d)
  iseqv := ⟨λ _ _ ↦ rfl, λ h x ↦ (h x).symm, λ h h0 x ↦ (h x).trans (h0 x)⟩
  add' := λ h h0 x ↦ by rw [← add_assoc, h0, add_right_comm, h, add_right_comm, add_assoc]

private lemma PeriodEquiv_map_eq [AddCommMonoid R]
    {f : R → S} {c d : R} (h : PeriodEquiv f c d) : f c = f d := by
  rw [← zero_add c, h, zero_add]


section

variable [NonUnitalSemiring R] [Add S] [IsCancelAdd S] (ι : S → R)
  [FunLike F R S] [GoodFunClass F ι] {f : F}
include ι

private lemma PeriodEquiv_mul_left (h : PeriodEquiv f c d) :
    ∀ x, PeriodEquiv f (x * c) (x * d) :=
  have h0 (x) : f (x * c) = f (x * d) := by
    rw [← good_def ι, ← good_def ι f x, PeriodEquiv_map_eq h, h]
  λ t x ↦ by rw [← add_right_inj, good_def ι, h0, ← mul_assoc, h0, good_def, mul_assoc]

private lemma PeriodEquiv_mul_right (h : PeriodEquiv f c d) :
    ∀ x, PeriodEquiv f (c * x) (d * x) :=
  have h0 (x) : f (c * x) = f (d * x) := by
    rw [← good_def ι, PeriodEquiv_map_eq h, add_comm c, h, add_comm x, good_def]
  λ t x ↦ by rw [add_comm, ← add_right_inj, good_def ι, h0,
    mul_assoc, h0, add_comm x, good_def, mul_assoc]

private lemma PeriodEquiv_mul (h : PeriodEquiv f c d) (h0 : PeriodEquiv f x y) :
    PeriodEquiv f (c * x) (d * y) :=
  (PeriodEquiv f).trans (PeriodEquiv_mul_right ι h x) (PeriodEquiv_mul_left ι h0 d)

private lemma PeriodEquiv_map (h : PeriodEquiv f (ι (f x)) (ι (f y))) : f x = f y := by
  have h0 := (map_map_zero_mul_map ι f x).trans (map_map_zero_mul_map ι f y).symm
  rwa [PeriodEquiv_map_eq (PeriodEquiv_mul_left ι h (ι (f 0))), add_right_inj] at h0

end


namespace GoodFun

variable [NonUnitalSemiring R] [Add S] [IsCancelAdd S] {ι : S → R} (f : GoodFun ι)

/-- The ring congruence induced by an `ι`-good map. -/
def inducedRingCon : RingCon R := { PeriodEquiv f with mul' := PeriodEquiv_mul ι }

/-- Definition of congruence relation given by `inducedRingCon`. -/
theorem inducedRingCon_def : f.inducedRingCon c d ↔ ∀ x, f (x + c) = f (x + d) := Iff.rfl

theorem inducedRingConEquiv_map_eq (h : f.inducedRingCon c d) : f c = f d :=
  PeriodEquiv_map_eq h


section

variable (rc : RingCon R) (hrc : f.inducedRingCon = rc)

/-- The induced non-periodic good quotient map using a copy of the ring congruence. -/
def Quotient' : NonperiodicGoodFun (rc.toQuotient ∘ ι) where
  toFun := Quotient.lift f λ _ _ h ↦ inducedRingConEquiv_map_eq f (hrc ▸ h)
  good_def' := Quotient.ind₂ (good_def ι f)
  period_imp_eq' := Quotient.ind₂ λ _ _ h ↦ Quot.sound (hrc ▸ λ x ↦ h x)

/-- Definition of the quotient map using a copy of the ring congruence. -/
lemma Quotient'_apply_mk (x : R) : f.Quotient' rc hrc x = f x := rfl

end


/-- The induced non-periodic good quotient map. -/
def Quotient : NonperiodicGoodFun (f.inducedRingCon.toQuotient ∘ ι) :=
  f.Quotient' f.inducedRingCon rfl

/-- Definition of the quotient map. -/
lemma Quotient_apply_mk (x : R) : f.Quotient x = f x := rfl

end GoodFun





/-! ### Correspondence between good functions and non-periodic good functions -/

section

variable [NonUnitalSemiring R] [Add S] [IsCancelAdd S]

theorem NonperiodicGoodFun.inducedRingCon_lift_eq
    {ι : S → R} {rc : RingCon R} (f : NonperiodicGoodFun (rc.toQuotient ∘ ι)) :
    f.Lift.inducedRingCon = rc := RingCon.ext λ c d ↦ by
  rw [← rc.eq, ← period_iff_eq (rc.toQuotient ∘ ι) (f := f)]
  exact Iff.symm Quotient.forall


namespace GoodFun

/-- Explicit correspondence between good functions with specified ring congruence
  and non-periodic good functions on the quotient of the congruence. -/
def FixedRingConCorrespondence (ι : S → R) (rc : RingCon R) :
    {f : GoodFun ι | f.inducedRingCon = rc} ≃ NonperiodicGoodFun (rc.toQuotient ∘ ι) where
  toFun f := f.1.Quotient' rc f.2
  invFun f := ⟨f.Lift, f.inducedRingCon_lift_eq⟩
  left_inv _ := rfl
  right_inv _ := NonperiodicGoodFun.ext (Quotient.ind λ _ ↦ rfl)

/-- Explicit correspondence between `ι`-good functions and non-periodic good functions. -/
def NonperiodicCorrespondence (ι : S → R) :
    GoodFun ι ≃ (rc : RingCon R) × NonperiodicGoodFun (rc.toQuotient ∘ ι) := calc
  _ ≃ (rc : RingCon R) × {f : GoodFun ι | f.inducedRingCon = rc} :=
    (Equiv.sigmaFiberEquiv inducedRingCon).symm
  _ ≃ (rc : RingCon R) × NonperiodicGoodFun (rc.toQuotient ∘ ι) :=
    Equiv.sigmaCongrRight (FixedRingConCorrespondence ι)

/-- Specification of `GoodFun.NonperiodicCorrespondence`. -/
theorem NonperiodicCorrespondence_def (ι : S → R) (f : GoodFun ι) :
    NonperiodicCorrespondence ι f = ⟨f.inducedRingCon, f.Quotient⟩ := rfl

/-- Specification of the inverse of `GoodFun.NonperiodicCorrespondence`. -/
theorem NonperiodicCorrespondence_symm_def (ι : S → R)
    {rc : RingCon R} (f : NonperiodicGoodFun (rc.toQuotient ∘ ι)) :
    (NonperiodicCorrespondence ι).symm ⟨rc, f⟩ = f.Lift := rfl

end GoodFun


@[deprecated]
theorem good_iff_exists_nonperiodicGood {ι : S → R} {f : R → S} :
    good ι f ↔ ∃ (rc : RingCon R) (g : rc.Quotient → S),
      nonperiodicGood (rc.toQuotient ∘ ι) g ∧ f = g ∘ rc.toQuotient := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩; exact ⟨f.inducedRingCon, f.Quotient, ⟨f.Quotient, rfl⟩, rfl⟩
  · rintro ⟨rc, g, ⟨g, rfl⟩, rfl⟩; exact ⟨g.Lift, rfl⟩

end
