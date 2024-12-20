/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6RingCon
import IMOSLLean4.IMO2017.A6.Extra.CentralInvolutive
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# IMO 2017 A6 (P2, Classifying good functions: division ring case)

We show that if $R$ is a division ring, then $f$ is $ι$-good iff
  either $f = 0$ or $f$ is non-periodic $ι$-good.
We also prove that the only $a ∈ Z(R)$ with $a^2 = 1$ are $±1$.

TODO: Generalize the implementation over simple rings, as the proof works as is.
-/

namespace IMOSL
namespace IMO2017A6

theorem RingCon_eq_bot_or_top [NonUnitalNonAssocRing R] [IsSimpleRing R] (rc : RingCon R) :
    rc = ⊥ ∨ rc = ⊤ :=
  (IsSimpleRing.simple.eq_bot_or_eq_top ⟨rc⟩).imp
    (congrArg TwoSidedIdeal.ringCon) (congrArg TwoSidedIdeal.ringCon)

theorem IsSimpleRing_exists_GoodFun_iff_zero_or_NonperiodicGoodFun
    [NonUnitalRing R] [IsSimpleRing R] [AddZeroClass G] [IsCancelAdd G]
    {ι : G → R} {f : R → G} : (∃ f' : GoodFun ι, f' = f) ↔
      (f = λ _ ↦ 0) ∨ (∃ f' : NonperiodicGoodFun ι, f' = f) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩; apply (RingCon_eq_bot_or_top f.inducedRingCon).symm.imp
    · intro h; ext x
      replace h : f.inducedRingCon x (ι (f 0) * ι (f 0)) := h ▸ trivial
      exact (GoodFun.inducedRingConEquiv_map_eq h).trans (map_incl_map_zero_mul_self ι f)
    · intro h; exact ⟨⟨f, λ c d (h0 : f.inducedRingCon c d) ↦ by rwa [h] at h0⟩, rfl⟩
  · rintro (rfl | ⟨f, rfl⟩); exacts [⟨GoodFun.zero ι, rfl⟩, ⟨f.toGoodFun, rfl⟩]

theorem DivisionRing_Central [DivisionRing R] (a : CentralInvolutive R) : a = 1 ∨ a = -1 :=
  (mul_self_eq_one_iff.mp a.mul_self_eq_one).imp CentralInvolutive.ext CentralInvolutive.ext
