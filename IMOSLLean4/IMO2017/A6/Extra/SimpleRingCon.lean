/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.RingTheory.SimpleRing.Defs

/-!
# Ring congruences of simple rings

We prove that if $R$ is a simple ring, then it only has (at most) two congruences.

TODO: Remove this when something similar gets to mathlib.
I'm guessing that this may get into the `Defs` file.
-/

namespace IMOSL
namespace Extra

theorem RingCon_eq_bot_or_top [NonUnitalNonAssocRing R] [IsSimpleRing R] (rc : RingCon R) :
    rc = ⊥ ∨ rc = ⊤ :=
  (IsSimpleRing.simple.eq_bot_or_eq_top ⟨rc⟩).imp
    (congrArg TwoSidedIdeal.ringCon) (congrArg TwoSidedIdeal.ringCon)
