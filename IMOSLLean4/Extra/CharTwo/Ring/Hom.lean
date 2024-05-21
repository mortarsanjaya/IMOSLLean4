/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.CharTwo.Ring.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Characteristic two instances through homomorphism

Let `φ : R → S` be a semiring homomorphism.
We show that if `R` has characteristic two, then so is `S`.
-/

namespace IMOSL
namespace Extra
namespace CharTwo

theorem ofRingHom [NonAssocSemiring R] [CharTwo R]
    [NonAssocSemiring S] (φ : R →+* S) : CharTwo S :=
  Semiring_of_two_eq_zero <| by rw [← one_add_one_eq_two, ← φ.map_one,
    ← φ.map_add, add_self_eq_zero, φ.map_zero]
