/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Bits
import Mathlib.Algebra.Order.Group.Int

/-!
# IMO 2017 C1

A rectangle in $ℕ^2$ is a subset of form $\{a, a + 1, …, a + w - 1\}
  × \{b, b + 1, …, b + h - 1\}$ for some $a, b, w, h ∈ ℕ$.
Given such rectangle, the quantity $w$ and $h$ are called the
  *width* and *height* of the rectangle, respectively.

A rectangle $R$ in $ℕ^2$ with odd width and height is
  partitioned into small rectangles.
Prove that there exists a small rectangle $R'$ with the following property:
  the distances from the sides of $R'$ to the respective sides
    of $R$ all have the same parity.
-/

namespace IMOSL
namespace IMO2017C1

open Finset

/-- The lattice rectangle `Ico a (a + w) × Ico b (b + h)`-/
def latticeRect (q : (ℕ × ℕ) × ℕ × ℕ) : Finset (ℕ × ℕ) :=
  Ico q.1.1 (q.1.1 + q.2.1) ×ˢ Ico q.1.2 (q.1.2 + q.2.2)



theorem sum_neg_one_pow_Ico (a : ℕ) :
    ∀ n : ℕ, (Ico a (a + n)).sum ((-1 : ℤ) ^ ·) = bif n.bodd then (-1 : ℤ) ^ a else 0
  | 0 => by rw [add_zero, Ico_self]; rfl
  | 1 => by rw [Nat.Ico_succ_singleton, sum_singleton]; rfl
  | n + 2 => by
      have h : a ≤ a + n := a.le_add_right n
      rw [← add_assoc, sum_Ico_succ_top (h.trans (a + n).le_succ),
        pow_succ', neg_one_mul, sum_Ico_succ_top h, sum_neg_one_pow_Ico a n,
        add_neg_cancel_right, Nat.bodd_add, Nat.bodd_two, Bool.xor_false]

/-- The weight of a finset in `ℕ × ℕ` -/
abbrev weight (S : Finset (ℕ × ℕ)) : ℤ := S.sum λ p ↦ (-1) ^ p.1 * (-1) ^ p.2

theorem disjiUnion_weight_eq {I : Finset ι} (h : (I : Set ι).PairwiseDisjoint F) :
    weight (I.disjiUnion F h) = I.sum λ i ↦ weight (F i) :=
  sum_disjiUnion _ _ _

theorem latticeRect_weight (q : (ℕ × ℕ) × ℕ × ℕ) :
    weight (latticeRect q) =
      bif (q.2.1.bodd && q.2.2.bodd) then ((-1 : ℤ) ^ (q.1.1 + q.1.2)) else 0 := by
  rw [weight, latticeRect, sum_product]; simp_rw [← mul_sum]
  rw [← sum_mul, sum_neg_one_pow_Ico, sum_neg_one_pow_Ico]
  cases q.2.1.bodd; exact zero_mul _
  cases q.2.2.bodd; exacts [mul_zero _, (pow_add _ _ _).symm]

theorem latticeRect_weight_pos_imp :
    (h : 0 < weight (latticeRect q)) →
      (q.2.1.bodd = true ∧ q.2.2.bodd = true) ∧ (q.1.1 + q.1.2).bodd = false := by
  rw [latticeRect_weight, ← Bool.and_eq_true]
  cases q.2.1.bodd && q.2.2.bodd
  · exact λ h ↦ absurd h (le_refl 0).not_gt
  · rw [neg_one_pow_eq_pow_mod_two (R := ℤ), Nat.mod_two_of_bodd]
    cases (q.1.1 + q.1.2).bodd
    exacts [λ _ ↦ ⟨rfl, rfl⟩, λ h ↦ absurd (by simp) h.not_gt]



/-- Final solution -/
theorem final_solution {I : Finset ι}
    (h : (I : Set ι).PairwiseDisjoint (latticeRect ∘ Q))
    (h0 : m.bodd = true ∧ n.bodd = true)
    (h1 : latticeRect ⟨⟨0, 0⟩, ⟨m, n⟩⟩ = I.disjiUnion (latticeRect ∘ Q) h) :
    ∃ i ∈ I, ((Q i).2.1.bodd = true ∧ (Q i).2.2.bodd = true)
      ∧ ((Q i).1.1 + (Q i).1.2).bodd = false := by
  suffices ∃ i ∈ I, 0 < weight (latticeRect (Q i))
    from this.elim λ i h3 ↦ ⟨i, h3.1, latticeRect_weight_pos_imp h3.2⟩
  replace h1 := congrArg weight h1
  rw [latticeRect_weight, disjiUnion_weight_eq, h0.1, h0.2, add_zero] at h1
  exact exists_lt_of_sum_lt (sum_const_zero.trans_lt (Int.zero_lt_one.trans_eq h1))
