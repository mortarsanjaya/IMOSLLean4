/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find

/-!
# IMO 2014 A1 (P1)

Let $(z_n)_{n ≥ 0}$ be an infinite sequence of positive integers.
1. Prove that there exists a unique non-negative integer $N$ such that
  $$ N z_N < \sum_{j = 0}^N z_j ≤ (N + 1) z_{N + 1}. $$
2. Prove that $N$ is positive.
3. **Extra**. Show that $\binom{N}{2} < z_0$.
-/

namespace IMOSL
namespace IMO2014A1

open Finset

def d (z : ℕ → ℤ) (n : ℕ) := (range (n + 1)).sum z - n * z n

theorem d_zero (z : ℕ → ℤ) : d z 0 = z 0 := by
  rw [d, sum_range_one, Int.cast_ofNat_Int, Int.zero_mul, Int.sub_zero]

theorem d_succ (z : ℕ → ℤ) (n : ℕ) :
    d z (n + 1) = (range (n + 1)).sum z - n * z (n + 1) := by
  rw [d, sum_range_succ, Int.natCast_add, Int.natCast_one,
    Int.add_mul, Int.one_mul, add_sub_add_right_eq_sub]

theorem d_one (z : ℕ → ℤ) : d z 1 = z 0 := by
  rw [d_succ, sum_range_one, Int.ofNat_zero, Int.zero_mul, Int.sub_zero]

variable {z : ℕ → ℤ} (h : StrictMono z)
include h

theorem main_lemma (n : ℕ) : d z (n + 1) ≤ d z n - n := by
  have X : (n : ℤ) * (z n + 1) = n * z n + n := by rw [Int.mul_add, Int.mul_one]
  rw [d_succ, d, sub_sub, ← X]; apply Int.sub_le_sub_left
  exact Int.mul_le_mul_of_nonneg_left (h n.lt_succ_self) (Int.ofNat_zero_le n)

theorem binom_bound : ∀ n, d z n ≤ z 0 - n.choose 2
  | 0 => ((d_zero z).trans (sub_zero _).symm).le
  | n + 1 => by
      rw [Nat.choose, Nat.choose_one_right, Int.natCast_add, ← sub_sub, sub_right_comm]
      exact Int.le_sub_right_of_add_le <|
        (Int.add_le_of_le_sub_right (main_lemma h n)).trans (binom_bound n)

theorem d_nonpos_of_big (h0 : (z 0).natAbs ≤ n.choose 2) : d z n ≤ 0 :=
  (binom_bound h n).trans (Int.sub_nonpos_of_le (Int.le_natAbs.trans (Int.ofNat_le.mpr h0)))

theorem d_nonpos_mono (h0 : d z n ≤ 0) : (h1 : n ≤ k) → d z k ≤ 0 :=
  Nat.le_induction h0 (λ x _ h2 ↦ (main_lemma h x).trans <|
    Int.sub_nonpos_of_le (h2.trans <| Int.ofNat_zero_le x)) k

omit h in
theorem d_one_pos (h0 : 0 < z 0) : 0 < d z 1 :=
  h0.trans_eq (d_one z).symm

/-- The desired unique `N` -/
def greatestDPos (_ : StrictMono z) : ℕ :=
  Nat.findGreatest (0 < d z ·) (z 0).natAbs.succ

variable (h0 : 0 < z 0)
include h0

theorem greatestDPos_is_d_pos : 0 < d z (greatestDPos h) :=
  Nat.findGreatest_spec (P := λ n ↦ 0 < d z n) (Nat.succ_pos _) (d_one_pos h0)

theorem greatestDPos_succ_not_d_pos : d z (greatestDPos h + 1) ≤ 0 :=
  le_of_not_gt <| Nat.findGreatest_is_greatest
      (P := λ n ↦ 0 < d z n) (greatestDPos h).lt_succ_self <|
    (Nat.findGreatest_le _).lt_or_eq.resolve_right λ h1 ↦
      (greatestDPos_is_d_pos h h0).not_ge <| d_nonpos_of_big h <|
        (congr_arg₂ Nat.choose h1.symm rfl).le.trans' <|
          (z 0).natAbs.choose_one_right.ge.trans (Nat.le_add_right _ _)

theorem eq_greatestDPos_iff :
    N = greatestDPos h ↔ 0 < d z N ∧ d z (N + 1) ≤ 0 :=
  have h1 := greatestDPos_is_d_pos h h0
  have h2 := greatestDPos_succ_not_d_pos h h0
  ⟨λ h3 ↦ h3 ▸ ⟨h1, h2⟩, λ h3 ↦ le_antisymm
    (le_of_not_gt λ h4 ↦ h3.1.not_ge (d_nonpos_mono h h2 h4))
    (le_of_not_gt λ h4 ↦ h1.not_ge (d_nonpos_mono h h3.2 h4))⟩





/-! ### Final solution -/

/-- Final solution, part 1: `N` is indeed the index we are looking for. -/
theorem final_solution_part1 :
    N = greatestDPos h ↔ ↑N * z N < (range (N + 1)).sum z ∧
      (range (N + 1)).sum z ≤ N * z (N + 1) := by
  rw [eq_greatestDPos_iff h h0, d_succ]
  refine and_congr Int.sub_pos ?_
  rw [← Int.le_add_iff_sub_le, Int.zero_add]

/-- Final solution, part 2: `N` is positive. -/
theorem final_solution_part2 : 0 < greatestDPos h :=
  Nat.pos_of_ne_zero λ h1 ↦ Nat.findGreatest_eq_zero_iff.mp
    h1 Nat.one_pos (Nat.succ_pos _) (d_one_pos h0)

/-- Final solution, extra: `C(N, 2) < z_0`, implemented as `C(N, 2) < (z 0).nat_abs`. -/
theorem final_solution_extra : (greatestDPos h).choose 2 < (z 0).natAbs :=
  lt_of_not_ge λ h1 ↦ (d_nonpos_of_big h h1).not_gt (greatestDPos_is_d_pos h h0)
