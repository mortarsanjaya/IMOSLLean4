/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Defs
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# IMO 2017 A6 (P2, Good functions and homomorphism)

Let `φ : R → S` be a homomorphism of rings.
Suppose that `φ` has a right inverse `ι : S → R` that is a group homomorphism.
Then for any `f : S → S`, `ι ∘ f ∘ φ` is a good function iff `f` is a good function.
-/

namespace IMOSL
namespace IMO2017A6

variable [Ring R] [Ring S] (φ : R →+* S) (ι : S →+ R) (h : Function.LeftInverse φ ι)
include h

def mk_of_HomPair (f : GoodFun S) : GoodFun R where
  toFun := λ x ↦ ι (f (φ x))
  good_def' := λ x y ↦ by
    simp only; rw [φ.map_mul, h, h, φ.map_add, φ.map_mul, ← ι.map_add, good_def]
