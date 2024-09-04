/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Archive.F2X.Ring
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Ring homomorphisms from `𝔽₂X`

In this file, we construct ring homomorphisms from `𝔽₂X`.
-/

namespace IMOSL
namespace IMO2012A5
namespace 𝔽₂X

variable [Semiring R] [Extra.CharTwo R] (r : R)

def cast (P : 𝔽₂X) : R := P.toFinset.sum λ n ↦ r ^ n

theorem cast_def (P : 𝔽₂X) : cast r P = P.toFinset.sum λ n ↦ r ^ n := rfl

theorem cast_Xpow (n : ℕ) : cast r (𝔽₂X.Xpow n) = r ^ n :=
  Finset.sum_singleton _ _

theorem cast_X : cast r X = r :=
  (cast_Xpow r 1).trans (pow_one r)

theorem cast_one : cast r 1 = 1 :=
  (cast_Xpow r 0).trans (pow_zero r)

theorem cast_zero : cast r 0 = 0 := rfl

theorem cast_add (P Q : 𝔽₂X) : cast r (P + Q) = cast r P + cast r Q :=
  Extra.CharTwo.symmDiff_sum_eq _ _ _

theorem cast_XpowMul_right (n : ℕ) : ∀ P, cast r (P.XpowMul n) = cast r P * r ^ n :=
  𝔽₂X.Xpow_add_induction
    (λ k ↦ by rw [XpowMul_Xpow, cast_Xpow, cast_Xpow, pow_add])
    (λ h h0 ↦ by rw [XpowMul_𝔽₂X_add, cast_add, h, h0, cast_add, add_mul])

theorem cast_mul (P : 𝔽₂X) : ∀ Q, cast r (P * Q) = cast r P * cast r Q :=
  𝔽₂X.Xpow_add_induction
    (λ n ↦ by rw [← XpowMul_eq_mul_Xpow, cast_XpowMul_right, cast_Xpow])
    (λ h h0 ↦ by rw [𝔽₂X.mul_add, cast_add, cast_add, h, h0, mul_add])

theorem cast_square (P : 𝔽₂X) : cast r P.square = cast r P ^ 2 := by
  rw [P.square_eq_mul_self, cast_mul, ← sq]

theorem cast_add_one (P : 𝔽₂X) : cast r (P + 1) = cast r P + 1 := by
  rw [cast_add, cast_one]

def castRingHom : 𝔽₂X →+* R :=
  { toFun := cast r
    map_one' := cast_one r
    map_mul' := cast_mul r
    map_zero' := cast_zero r
    map_add' := cast_add r }
