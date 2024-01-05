/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.ZMod.Basic

namespace IMOSL
namespace IMO2020N5

/-- `unitOfCoprime` always sends `1 : ℕ` to `1 : (ZMod p)ˣ` -/
lemma unitOfCoprime_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left p) = 1 :=
  Units.val_eq_one.mp Nat.cast_one


section ZModUnit_toPNat

variable (hp : Nat.Prime p) (x : (ZMod p)ˣ)

/-- The value of a unit in `(ZMod p)ˣ` is positive if `p` is prime. -/
lemma ZModUnit_val_pos : 0 < x.val.val := by
  rw [Nat.pos_iff_ne_zero, Ne.def, ZMod.val_eq_zero]
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  exact Units.ne_zero x

/-- Embedding `(ZMod p)ˣ → ℕ+` defined by simply taking values -/
def ZModUnit_toPNat : ℕ+ := ⟨x.val.val, ZModUnit_val_pos hp x⟩

theorem ZModUnit_toPNat_val : (ZModUnit_toPNat hp x).val = x.val.val := rfl

theorem not_Nat_dvd_ZModUnit_toPNat : ¬p ∣ ZModUnit_toPNat hp x :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  Nat.not_dvd_of_pos_of_lt (ZModUnit_val_pos hp x) (ZMod.val_lt _)

theorem not_dvd_ZModUnit_toPNat : ¬(⟨p, hp.pos⟩ : ℕ+) ∣ ZModUnit_toPNat hp x :=
  mt PNat.dvd_iff.mp (not_Nat_dvd_ZModUnit_toPNat _ _)

end ZModUnit_toPNat
