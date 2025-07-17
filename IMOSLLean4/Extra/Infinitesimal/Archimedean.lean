/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.Infinitesimal.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Infinitesimal elements of an archimedean ring

Let `R` be an archimedean ordered ring.
We prove that the only infinitesimal element of `R` is `0`.
-/

namespace IMOSL
namespace Extra
namespace Infinitesimal

theorem zero_of_Archimedean [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] {ε : R} (h : Infinitesimal ε) : ε = 0 :=
  (abs_nonneg ε).eq_or_lt.elim (λ h0 ↦ abs_eq_zero.mp h0.symm)
    (λ h0 ↦ (Archimedean.arch 1 h0).elim λ k h1 ↦ absurd (h k) h1.not_gt)
