/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Basic

namespace IMOSL
namespace IMO2020N5

/-- Extra lemma: given `n : ℕ+` such that `n > 1`, we have `n - 1 < n` -/
lemma PNat_pred_lt_self {n : ℕ+} (h : 1 < n) : n - 1 < n :=
  ((n - 1).lt_add_left 1).trans_eq (PNat.add_sub_of_lt h)
