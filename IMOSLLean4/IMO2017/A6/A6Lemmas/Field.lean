/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Lemmas.Basic
import Mathlib.Algebra.Field.Defs

/-!
# IMO 2017 A6 (P2, Good functions over a division ring)

We prove one lemma about good functions when `R` is a division ring.
-/

namespace IMOSL
namespace IMO2017A6

variable [DivisionRing R] [AddGroup S]

/-- Good functions on division rings: a formula -/
theorem DivRing_inv_formula (ι : S → R) [FunLike F R S] [GoodFunClass F ι]
    (f : F) {c : R} (h : c ≠ 0) :
    f (ι (f (c + 1)) * ι (f (c⁻¹ + 1))) = 0 := by
  rw [eq_sub_of_add_eq (good_def ι f _ _), sub_eq_zero,
    add_one_mul c, mul_add_one c, mul_inv_cancel₀ h, add_comm 1]
