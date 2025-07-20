/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2017.A6.A6RingCon.Basic
import Mathlib.RingTheory.SimpleRing.Defs

/-!
# IMO 2017 A6 (P2, Classifying good functions: simple ring case)

We show that if $R$ is a simple ring, then $f$ is $ι$-good iff
  either $f = 0$ or $f$ is non-periodic $ι$-good.
-/

namespace IMOSL
namespace IMO2017A6

theorem RingCon_eq_bot_or_top [NonUnitalNonAssocRing R] [IsSimpleRing R] (rc : RingCon R) :
    rc = ⊥ ∨ rc = ⊤ :=
  (IsSimpleRing.simple.eq_bot_or_eq_top ⟨rc⟩).imp
    (congrArg TwoSidedIdeal.ringCon) (congrArg TwoSidedIdeal.ringCon)

instance [Add R] [Mul R] : Subsingleton (⊤ : RingCon R).Quotient :=
  ⟨Quotient.ind₂ λ _ _ ↦ Quot.sound trivial⟩

theorem SimpleRing_IsGoodFun_iff_zero_or_Nonperiodic
    [NonUnitalRing R] [IsSimpleRing R] [AddZeroClass G] [IsCancelAdd G] {ι : G → R} :
    IsGoodFun ι f ↔ f = 0 ∨ IsNonperiodicGoodFun ι f := by
  refine ⟨?_, λ h ↦ h.elim (λ h ↦ h ▸ IsGoodFun.zero) (λ h ↦ h.toIsGoodFun)⟩
  rw [IsGoodFun.iff]; rintro ⟨g, rfl⟩
  exact (RingCon_eq_bot_or_top g.inducedRingCon).symm.imp
    (λ h ↦ congrArg DFunLike.coe (GoodFun.eq_zero_of_inducedRingCon h))
    GoodFun.nonperiodic_of_inducedRingCon
