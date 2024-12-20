/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Defs

/-!
# `n`-torsion free groups

We define a typeclass saying that a group is $n$-torsion-free for some $n ∈ ℕ$.

TODO: Remove this when something similar gets to mathlib.
-/

namespace IMOSL
namespace Extra

class IsTorsionFreeBy (G) [AddMonoid G] (n : ℕ) : Prop where
  nsmul_left_cancel : ∀ x y : G, n • x = n • y → x = y

variable [AddMonoid G] [IsTorsionFreeBy G n]

theorem nsmul_left_cancel {x y : G} (h : n • x = n • y) : x = y :=
  IsTorsionFreeBy.nsmul_left_cancel x y h

theorem nsmul_eq_zero_imp {x : G} (h : n • x = 0) : x = 0 :=
  nsmul_left_cancel (h.trans (nsmul_zero n).symm)
