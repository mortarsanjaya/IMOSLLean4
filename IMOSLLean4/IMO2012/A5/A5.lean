/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5AnswerCheck
import IMOSLLean4.IMO2012.A5.Case1.Main
import IMOSLLean4.IMO2012.A5.Case2.Main

/-! # IMO 2012 A5 -/

namespace IMOSL
namespace IMO2012A5

variable {R S : Type _} [CommRing R] [Field S] {f : R → S}

theorem IsAnswer_of_good (h : good f) : IsAnswer f :=
  (em' <| f 0 = -1).elim
    (λ h0 ↦ (eq_zero_of_map_zero_ne_neg_one h h0).symm ▸ IsAnswer.of_zero)
    (λ h0 ↦ (em' <| f (-1) = 0).elim (case1_IsAnswer h)
      (λ h1 ↦ case2_IsAnswer h h1 h0))

/-- Final solution -/
theorem final_solution : good f ↔ IsAnswer f :=
  ⟨IsAnswer_of_good, good_of_IsAnswer⟩
