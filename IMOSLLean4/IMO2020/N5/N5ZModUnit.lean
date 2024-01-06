/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.N5Basic
import IMOSLLean4.IMO2020.N5.Extra.EvenMonoidHom.Basic
import IMOSLLean4.IMO2020.N5.Nat.Lemma2
import IMOSLLean4.IMO2020.N5.Extra.ZModUnitProp
import Mathlib.Data.PNat.Prime

/-!
# IMO 2020 N5 (Nice Primes to Even Homomorphism `(ZMod p)ˣ →* M`)

This file proves the following crucial result:
* Let `f : ℕ+ →* M` and `p : ℕ+` be an `f`-nice prime.
  Then `f` restricts to an even homomorphism `φ : EvenMonoidHom (ZMod p)ˣ M`.
It is a consequence of Lemma 2 from the LaTeX file.
We implement the same result over `MulMap M` as an intermediate step.
-/

namespace IMOSL
namespace IMO2020N5

namespace MulMap

variable [CancelCommMonoid M] (f : MulMap M)

def toZModUnitMap (p : ℕ) (x : (ZMod p)ˣ) : M := f x.val.val

lemma toZModUnitMap_one (h : 1 < p) : toZModUnitMap f p 1 = 1 := by
  rw [toZModUnitMap, Units.val_one, ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt h, f.map_one]

variable (hp : Nat.Prime p) (h : Nat.nice f p)

lemma toZModUnitMap_mul (x y : (ZMod p)ˣ) :
    toZModUnitMap f p (x * y) = toZModUnitMap f p x * toZModUnitMap f p y := by
  unfold toZModUnitMap
  rw [Units.val_mul, ZMod.val_mul]
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact Nat.nice_mul_mod_of_lt hp h (ZModUnit_val_pos hp x)
    x.val.val_lt (ZModUnit_val_pos hp y) y.val.val_lt

lemma toZModUnitMap_neg_one : toZModUnitMap f p (-1) = 1 := by
  rw [toZModUnitMap, Units.val_neg, Units.val_one]
  rcases p with _ | q
  · exact absurd hp Nat.not_prime_zero
  · rw [ZMod.val_neg_one, ← f.map_one]
    exact h q 1 (Nat.succ_lt_succ_iff.mp hp.one_lt) Nat.one_pos rfl

def toZModUnitEvenHom : EvenMonoidHom (ZMod p)ˣ M :=
  { toFun := toZModUnitMap f p
    map_one' := toZModUnitMap_one f hp.one_lt
    map_mul' := toZModUnitMap_mul f hp h
    map_neg_one' := toZModUnitMap_neg_one f hp h }

lemma toZModUnitEvenHom_apply (x : (ZMod p)ˣ) :
    toZModUnitEvenHom f hp h x = f x.val.val := rfl

end MulMap





section PNatHom

variable [CancelCommMonoid M] {φ : ℕ+ →* M}
  {p : Nat.Primes} (h : nice φ.toFun p)

def PNatHom_toZModUnitEvenHom : EvenMonoidHom (ZMod p)ˣ M :=
  (MulMap.ofPNatHom φ).toZModUnitEvenHom p.2 (niceNat_of_nice h)

lemma PNatHom_toZModUnitEvenHom_apply (x : (ZMod p)ˣ) :
    PNatHom_toZModUnitEvenHom h x = φ (ZModUnit_toPNat p.2 x) :=
  MulMap.ofPNatHom_spec φ ⟨_, _⟩

end PNatHom
