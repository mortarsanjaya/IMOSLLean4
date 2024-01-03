/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Extra.PAdicValCompl.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Embedding of `p`-adic complement into `(ZMod p)ˣ`

Let `p : ℕ+` be a prime.
We construct the function that sends `n : ℕ+` into the
  image of `p`-adic complement `n/p^ν_p(n)` in `(ZMod p)ˣ`.
-/

namespace IMOSL
namespace IMO2020N5

/-- `unitOfCoprime` always sends `1 : ℕ` to `1 : (ZMod p)ˣ` -/
lemma unitOfCoprime_one (h : Nat.Coprime 1 p) : ZMod.unitOfCoprime 1 h = 1 :=
  Units.val_eq_one.mp Nat.cast_one



namespace padicComplPNat

variable (p : Nat.Primes)

def ZModUnit (n : ℕ+) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime (padicComplPNat p n) (coprimeNat p n)

lemma ZModUnit_one : ZModUnit p 1 = 1 :=
  unitOfCoprime_one _

lemma ZModUnit_coeZMod (n : ℕ+) :
    (ZModUnit p n).val = (padicComplPNat p n).val :=
  ZMod.coe_unitOfCoprime _ _

lemma ZModUnit_mul (x y : ℕ+) :
    ZModUnit p (x * y) = ZModUnit p x * ZModUnit p y := by
  rw [← Units.eq_iff, ZModUnit_coeZMod, Units.val_mul, mul,
    PNat.mul_coe, Nat.cast_mul, ZModUnit_coeZMod, ZModUnit_coeZMod]

def ZModUnitHom : ℕ+ →* (ZMod p)ˣ :=
  { toFun := ZModUnit p
    map_one' := ZModUnit_one p
    map_mul' := ZModUnit_mul p }

lemma ZModUnit_self : ZModUnit p p = 1 := by
  simp_rw [ZModUnit, self]; exact unitOfCoprime_one _

lemma ZModUnit_pred : ZModUnit p (p - 1) = -1 := by
  rw [← Units.eq_iff, ZModUnit_coeZMod, padicComplPNat.pred, PNat.sub_coe]
  change ((if 1 < (p : ℕ) then (p : ℕ).pred else 1 : ℕ) : ZMod p) = -1
  rw [if_pos p.2.one_lt, eq_neg_iff_add_eq_zero, ← Nat.cast_succ,
    Nat.succ_pred p.2.ne_zero, ZMod.nat_cast_self]

end padicComplPNat
