/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.F2X.Defs
import Mathlib.Algebra.Ring.Defs

/-! # `𝔽₂[X]` is a ring -/

namespace IMOSL
namespace IMO2012A5
namespace 𝔽₂X

instance : CommRing 𝔽₂X :=
  { 𝔽₂X.instAddCommGroup with
    zero_mul := 𝔽₂X.zero_mul
    mul_zero := 𝔽₂X.mul_zero
    one_mul := 𝔽₂X.one_mul
    mul_one := 𝔽₂X.mul_one
    mul_comm := 𝔽₂X.mul_comm
    mul_assoc := 𝔽₂X.mul_assoc
    left_distrib := 𝔽₂X.mul_add
    right_distrib := 𝔽₂X.add_mul
    npow := λ n P ↦ P.natPow n
    npow_zero := 𝔽₂X.natPow_zero
    npow_succ := λ n P ↦ P.natPow_succ n }
