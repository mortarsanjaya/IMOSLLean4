/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Defs
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

### TODO

Tbe function `GoodFun.Lift` might be problematic here.
Change it to something like `Lift (f : GoodFun β) (_ : β = ι)` instead.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Extension of good functions -/

namespace GoodFun

variable [Add R] [Mul R] [Add G] {ι : G → R} {rc : RingCon R}

/-- Extension of an `ι`-good function via the quotient map. -/
def Lift (f : GoodFun (rc.toQuotient ∘ ι)) : GoodFun ι where
  toFun x := f x
  good_def' x y := good_def (rc.toQuotient ∘ ι) f x y

theorem lift_def (f : GoodFun (rc.toQuotient ∘ ι)) (x) : f.Lift x = f x := rfl

end GoodFun





/-! ### Projecting down by period congruence -/

def PeriodEquiv [AddCommSemigroup R] (f : R → α) : AddCon R where
  r c d := ∀ x, f (x + c) = f (x + d)
  iseqv := ⟨λ _ _ ↦ rfl, λ h x ↦ (h x).symm, λ h h0 x ↦ (h x).trans (h0 x)⟩
  add' h h0 x := by rw [← add_assoc, h0, add_right_comm, h, add_right_comm, add_assoc]

lemma PeriodEquiv_map_eq [AddCommMonoid R] {f : R → α} (h : PeriodEquiv f c d) :
    f c = f d := by
  simpa only [zero_add] using h 0


namespace GoodFun

variable [AddCommMonoid R] [Semigroup R] [Add G] [IsCancelAdd G] {ι : G → R}

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
theorem inducedRingCon_def {f : GoodFun ι} {c d} :
    f.inducedRingCon c d ↔ ∀ x, f (x + c) = f (x + d) := Iff.rfl

theorem inducedRingConEquiv_map_eq {f : GoodFun ι} (h : inducedRingCon f c d) : f c = f d :=
  PeriodEquiv_map_eq h


section

variable (f : GoodFun ι) (rc : RingCon R) (hrc : f.inducedRingCon = rc)

/-- The induced non-periodic good quotient map using a copy of the ring congruence. -/
def Quotient' : NonperiodicGoodFun (rc.toQuotient ∘ ι) where
  toFun := Quotient.lift f λ _ _ h ↦ inducedRingConEquiv_map_eq (hrc ▸ h)
  good_def' := Quotient.ind₂ (good_def ι f)
  period_imp_eq' := Quotient.ind₂ λ _ _ h ↦ Quot.sound (hrc ▸ λ x ↦ h x)

/-- Definition of the quotient map using a copy of the ring congruence. -/
lemma Quotient'_apply_mk (x : R) : f.Quotient' rc hrc x = f x := rfl

end


/-- The induced non-periodic good quotient map. -/
def Quotient (f : GoodFun ι) : NonperiodicGoodFun (f.inducedRingCon.toQuotient ∘ ι) :=
  f.Quotient' f.inducedRingCon rfl

/-- Definition of the quotient map. -/
lemma Quotient_apply_mk (f : GoodFun ι) (x : R) : f.Quotient x = f x := rfl

end GoodFun





/-! ### Correspondence between good functions and non-periodic good functions -/

theorem NonperiodicGoodFun.inducedRingCon_lift_eq
    [AddCommMonoid R] [Semigroup R] [Add G] [IsCancelAdd G] {ι : G → R}
    {rc : RingCon R} (f : NonperiodicGoodFun (rc.toQuotient ∘ ι)) :
    f.Lift.inducedRingCon = rc := by
  refine RingCon.ext λ c d ↦ ?_
  rw [← rc.eq, ← period_iff_eq (rc.toQuotient ∘ ι) (f := f)]
  exact Iff.symm Quotient.forall


namespace GoodFun

section

variable [AddCommMonoid R] [Semigroup R] [Add G] [IsCancelAdd G] (ι : G → R)
include ι

/-- Explicit correspondence between good functions with specified ring congruence
  and non-periodic good functions on the quotient of the congruence. -/
def FixedRingConCorrespondence (rc : RingCon R) :
    {f : GoodFun ι | f.inducedRingCon = rc} ≃ NonperiodicGoodFun (rc.toQuotient ∘ ι) where
  toFun f := f.1.Quotient' rc f.2
  invFun f := ⟨f.Lift, f.inducedRingCon_lift_eq⟩
  left_inv _ := rfl
  right_inv _ := NonperiodicGoodFun.ext (Quotient.ind λ _ ↦ rfl)

/-- Explicit correspondence between `ι`-good functions and non-periodic good functions. -/
def NonperiodicCorrespondence :
    GoodFun ι ≃ (rc : RingCon R) × NonperiodicGoodFun (rc.toQuotient ∘ ι) := calc
  _ ≃ (rc : RingCon R) × {f : GoodFun ι | f.inducedRingCon = rc} :=
    (Equiv.sigmaFiberEquiv inducedRingCon).symm
  _ ≃ (rc : RingCon R) × NonperiodicGoodFun (rc.toQuotient ∘ ι) :=
    Equiv.sigmaCongrRight (FixedRingConCorrespondence ι)

/-- Specification of `GoodFun.NonperiodicCorrespondence`. -/
theorem NonperiodicCorrespondence_def (f : GoodFun ι) :
    NonperiodicCorrespondence ι f = ⟨f.inducedRingCon, f.Quotient⟩ := rfl

/-- Specification of the inverse of `GoodFun.NonperiodicCorrespondence`. -/
theorem NonperiodicCorrespondence_symm_def
    {rc : RingCon R} (f : NonperiodicGoodFun (rc.toQuotient ∘ ι)) :
    (NonperiodicCorrespondence ι).symm ⟨rc, f⟩ = f.Lift := rfl

end


section

variable [Semiring R] [AddZeroClass G] [IsCancelAdd G] (ι : G →+ R)
include ι

/-- Group homomorphism version of `NonperiodicCorrespondence`. -/
def AddMonoidHomNonperiodicCorrespondence :
    GoodFun ι ≃ (rc : RingCon R) × NonperiodicGoodFun (rc.mk'.toAddMonoidHom.comp ι) :=
  NonperiodicCorrespondence ι

/-- Specification of `GoodFun.AddMonoidHomNonperiodicCorrespondence`. -/
theorem AddMonoidHomNonperiodicCorrespondence_def (f : GoodFun ι) :
    AddMonoidHomNonperiodicCorrespondence ι f = ⟨f.inducedRingCon, f.Quotient⟩ := rfl

/-- Specification of the inverse of `GoodFun.AddMonoidHomNonperiodicCorrespondence`. -/
theorem AddMonoidHomNonperiodicCorrespondence_symm_def
    {rc : RingCon R} (f : NonperiodicGoodFun (rc.mk'.toAddMonoidHom.comp ι)) :
    (AddMonoidHomNonperiodicCorrespondence ι).symm ⟨rc, f⟩ = f.Lift := rfl

end

end GoodFun
