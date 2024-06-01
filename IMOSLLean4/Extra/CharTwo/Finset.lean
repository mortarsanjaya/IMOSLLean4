/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.CharTwo.Defs
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# Characteristic two and big operators over `Finset`

We prove several lemmas about sums over monoids and ring of characteristic two.
-/

namespace IMOSL
namespace Extra

/-! ### Extra lemmas -/

section

variable [DecidableEq ι] {i : ι} {S : Finset ι}

lemma symmDiff_singleton_eq_insert (h : i ∉ S) : symmDiff {i} S = insert i S :=
  (symmDiff_eq_sup _ _).mpr (Finset.disjoint_singleton_left.mpr h)

lemma symmDiff_singleton_eq_erase (h : i ∈ S) : symmDiff {i} S = S.erase i := by
  have h0 : {i} \ S = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr λ c h0 ↦ Finset.mem_singleton.mp h0 ▸ h
  rw [symmDiff, Finset.sdiff_singleton_eq_erase, h0]
  exact bot_sup_eq _

end





/-! ### `CharTwo` -/

namespace CharTwo

section

variable [AddCommMonoid M] [CharTwo M] [DecidableEq ι] (f : ι → M)

lemma symmDiff_singleton_sum_eq (i : ι) (S : Finset ι) :
    (symmDiff {i} S).sum f = f i + S.sum f := by
  by_cases h : i ∈ S
  · rw [symmDiff_singleton_eq_erase h, ← S.add_sum_erase f h, CharTwo.add_add_cancel_left]
  · rw [symmDiff_singleton_eq_insert h, Finset.sum_insert h]

lemma symmDiff_sum_eq (S T : Finset ι) : (symmDiff S T).sum f = S.sum f + T.sum f := by
  revert T; apply Finset.induction
  · have h : symmDiff S ∅ = S := by exact symmDiff_bot _
    rw [Finset.sum_empty, add_zero, h]
  · intro i T h h0
    rw [Finset.sum_insert h, add_left_comm, ← h0, ← symmDiff_singleton_eq_insert h,
      symmDiff_left_comm, symmDiff_singleton_sum_eq]

end
