/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.ExcellentFun.AddHom
import Mathlib.RingTheory.Congruence.Defs

/-!
# Excellent functions and quotient ring

Let `R` be a ring, `G` be an abelian group, and `rc : RingCon R`.
Then any excellent function `rc.Quotient → G` lifts
  injectively into an excellent functions `R → G`.
We also show that an `IsOfAddMonoidHomSurjective R G` instance implies an
  `IsOfAddMonoidHomSurjective rc.Quotient G` instance for each `rc : RingCon R`.
-/

namespace IMOSL
namespace IMO2017A6
namespace ExcellentFun

variable [NonAssocRing R]

/-- Lift an excellent function `R/I → G` to an excellent function `R/G`. -/
def RingConLift [Add G] {rc : RingCon R} (f : ExcellentFun rc.Quotient G) :
    ExcellentFun R G where
  toFun x := f x
  excellent_def' x y := f.excellent_def' x y

theorem RingConLift_injective [Add G] {rc : RingCon R} :
    (RingConLift (rc := rc) (G := G)).Injective :=
  λ _ _ h ↦ ExcellentFun.ext (Quotient.ind (ExcellentFun.ext_iff.mp h))

def RingConLiftHom [AddCommMonoid G] (rc : RingCon R) :
    ExcellentFun rc.Quotient G →+ ExcellentFun R G where
  toFun := RingConLift
  map_zero' := rfl
  map_add' _ _ := rfl

theorem RingConLiftHom_injective [AddCommMonoid G] {rc : RingCon R} :
    Function.Injective (RingConLiftHom rc (G := G)) :=
  RingConLift_injective

instance [AddZeroClass G] [IsOfAddMonoidHomSurjective R G] (rc : RingCon R) :
    IsOfAddMonoidHomSurjective rc.Quotient G where
  ofAddMonoidHom_surjective f := by
    obtain ⟨φ, h⟩ := ofAddMonoidHom_surjective f.RingConLift
    replace h (x : R) : φ x = f x := ExcellentFun.ext_iff.mp h x
    have h0 : f 0 = 0 := (h 0).symm.trans φ.map_zero
    replace h (x y : R) : f ((x + y : R)) = f x + f y := by simp only [← h, φ.map_add]
    exact ⟨⟨⟨f, h0⟩, Quotient.ind₂ h⟩, rfl⟩
