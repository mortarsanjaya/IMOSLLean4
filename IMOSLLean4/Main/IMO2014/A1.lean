/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# IMO 2014 A1 (P1)

Let $z_0 < z_1 < z_2 < …$ be an infinite sequence of positive integers.
Prove that there exists a unique positive integer $n$ such that
$$ n z_n < \sum_{j = 0}^n z_j ≤ n z_{n + 1}. $$

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2014SL.pdf).
-/

namespace IMOSL
namespace IMO2014A1

open Finset

/-- Given a strictly increasing function `z : ℕ → ℤ`, the function `d : ℕ → ℤ`
  defined by `d_n = ∑_{i = 0}^{n + 1} z_i - nz_{n + 1}` is strictly decreasing. -/
theorem d_strictAnti {z : ℕ → ℤ} (hz : StrictMono z) :
    StrictAnti (λ n ↦ ∑ i ∈ range (n + 2), z i - (n + 1 : ℕ) * z (n + 1)) := by
  refine strictAnti_nat_of_succ_lt λ n ↦ ?_
  rw [sum_range_succ, add_sub_right_comm, sub_add, Int.sub_lt_sub_left_iff,
    Int.natCast_succ (n + 1), Int.add_mul _ _ (z (n + 2)), Int.one_mul, Int.add_sub_cancel]
  exact Int.mul_lt_mul_of_pos_left (hz (Nat.lt_succ_self _))
    (Int.natCast_pos.mpr (Nat.succ_pos n))

/-- Given a strictly decreasing sequence `d : ℕ → ℤ` such that `d_0 > 0`,
  there exists a unique index `n` such that `d_n > 0 ≥ d_{n + 1}`. -/
theorem existsUnique_d_pos_d_succ_neg {d : ℕ → ℤ} (hd : StrictAnti d) (hd0 : d 0 > 0) :
    ∃! n, d n > 0 ∧ d (n + 1) ≤ 0 := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  ---- Existence: if not, then `d_n > 0` and `d_n ≤ d_0 - n` for all `n`; contradiction.
  · by_contra! hd1
    replace hd1 : ∀ n, d n > 0 := Nat.rec hd0 hd1
    replace hd (n) : d n ≤ d 0 - n := by
      induction n with | zero => exact Int.le.intro 0 rfl | succ n n_ih => ?_
      rw [Int.natCast_succ, ← Int.sub_sub, Int.le_sub_one_iff]
      exact (hd (Nat.lt_add_one n)).trans_le n_ih
    lift d 0 to ℕ using hd0.le with k hk
    exact Int.not_le_of_gt (hd1 k) ((hd _).trans_eq (Int.sub_self _))
  ---- Uniqueness: if `n < N` then `d_n < 0 → d_N < 0` and `d_N ≥ 0 → d_n ≥ 0`.
  · rintro n N ⟨hn, hn0⟩ ⟨hN, hN0⟩
    replace hd : Antitone d := hd.antitone
    by_contra h; obtain h0 | h0 : n < N ∨ N < n := Nat.lt_or_gt_of_ne h
    exacts [Int.not_le_of_gt hN ((hd h0).trans hn0), Int.not_le_of_gt hn ((hd h0).trans hN0)]

/-- Final solution -/
theorem final_solution {z : ℕ → ℤ} (hz : StrictMono z) (hz0 : z 0 > 0) :
    ∃! n > 0, n * z n < ∑ i ∈ range (n + 1), z i ∧
      ∑ i ∈ range (n + 1), z i ≤ n * z (n + 1) := by
  ---- Set `d_n = ∑_{i = 0}^n z_i - nz_n` for all `n : ℕ`.
  let d (n : ℕ) : ℤ := ∑ i ∈ range (n + 1), z i - n * z n
  ---- It suffices to show there exists a unique index `n > 0` with `d_n > 0 ≥ d_{n + 1}`.
  suffices ∃! n > 0, 0 < d n ∧ d (n + 1) ≤ 0 by
    conv at this =>
      right; ext n; right; rw [Int.sub_pos]
      right; rw [← not_lt, Int.sub_pos, Int.natCast_succ, sum_range_succ,
        Int.add_mul, Int.one_mul, Int.add_lt_add_iff_right, not_lt]
    exact this
  ---- Since `d_1 > d_2 > …`, there is a unique index `n` with `d_{n + 1} > 0 ≥ d_{n + 2}`.
  obtain ⟨n, hn, hn0⟩ : ∃! n, d (n + 1) > 0 ∧ d (n + 2) ≤ 0 := by
    refine existsUnique_d_pos_d_succ_neg (d_strictAnti hz) (?_ : _ - _ > (0 : ℤ))
    rwa [sum_range_succ, sum_range_one, Int.natCast_one, Int.one_mul, add_sub_cancel_right]
  ---- Now picking `n + 1` in place of `n` works.
  refine ⟨n + 1, ⟨Nat.succ_pos n, hn⟩, λ y hy ↦ ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, y = N + 1 := Nat.exists_eq_succ_of_ne_zero hy.1.ne.symm
  exact congrArg (· + 1) (hn0 N hy.2)
