/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Basic

/-!
# IMO 2014 A1 (P1)

Let $(z_n)_{n ≥ 0}$ be an infinite sequence of positive integers.
Prove that there exists a unique non-negative integer $N$ such that
$$ N z_N < \sum_{j = 0}^N z_j \leq (N + 1) z_{N + 1}. $$
Furthermore, prove that $N$ is positive.

**Extra**: Show that $\binom{N}{2} < z_0$.
-/

namespace IMOSL
namespace IMO2014A1

open Finset

def d (z : ℕ → ℤ) (n : ℕ) := (range (n + 1)).sum z - n * z n

theorem d_zero (z : ℕ → ℤ) : d z 0 = z 0 := by
  rw [d, sum_range_one, Nat.cast_zero, zero_mul, sub_zero]

theorem d_succ (z : ℕ → ℤ) (n : ℕ) :
    d z (n + 1) = (range (n + 1)).sum z - n * z (n + 1) := by
  rw [d, sum_range_succ, Nat.cast_succ,
    add_one_mul, add_sub_add_right_eq_sub]

theorem d_one (z : ℕ → ℤ) : d z 1 = z 0 := by
  rw [d_succ, sum_range_one, Nat.cast_zero, zero_mul, sub_zero]

variable {z : ℕ → ℤ} (h : StrictMono z)

theorem main_lemma (n : ℕ) : d z (n + 1) ≤ d z n - n :=
  (d_succ z n).trans_le <|
    (sub_sub _ _ _).ge.trans' <|
      sub_le_sub_left
        ((mul_add_one _ _).symm.trans_le <|
          mul_le_mul_of_nonneg_left (Int.add_one_le_iff.mpr <| h n.lt_succ_self) n.cast_nonneg)
        _

theorem binom_bound : ∀ n, d z n ≤ z 0 - n.choose 2
  | 0 => ((d_zero z).trans (sub_zero _).symm).le
  | n + 1 =>
    (main_lemma h n).trans <|
      (sub_le_sub_right (binom_bound n) _).trans_eq <|
        (sub_sub _ _ _).trans <|
          congr_arg₂ _ rfl <|
            (Int.ofNat_add _ _).symm.trans <|
              congr_arg _ <| (add_comm _ _).trans <| congr_arg₂ _ n.choose_one_right.symm rfl

theorem d_nonpos_of_big {n : ℕ} (h0 : (z 0).natAbs ≤ n.choose 2) : d z n ≤ 0 :=
  (binom_bound h n).trans <|
    Int.sub_nonpos_of_le <|
      (le_abs_self _).trans <| (z 0).coe_natAbs.symm.trans_le <| Int.ofNat_le.mpr h0

theorem d_nonpos_mono {n : ℕ} (h0 : d z n ≤ 0) {k : ℕ} (h1 : n ≤ k) : d z k ≤ 0 :=
  Nat.le_induction h0
    (fun x _ h2 => (main_lemma h x).trans <| Int.sub_nonpos_of_le <| h2.trans x.cast_nonneg) k h1

theorem d_one_pos (h0 : 0 < z 0) : 0 < d z 1 :=
  h0.trans_eq (d_one z).symm

/-- The desired unique `N` -/
def greatestDPos (_ : StrictMono z) : ℕ :=
  Nat.findGreatest (0 < d z ·) (z 0).natAbs.succ

variable (h0 : 0 < z 0)

theorem greatestDPos_is_d_pos : 0 < d z (greatestDPos h) :=
  let P n := 0 < d z n
  let h2 : P 1 := d_one_pos h0
  Nat.findGreatest_spec (P := P) (Nat.succ_pos _) h2

theorem greatestDPos_succ_not_d_pos : d z (greatestDPos h + 1) ≤ 0 :=
  le_of_not_lt <|
    Nat.findGreatest_is_greatest (greatestDPos h).lt_succ_self <|
      (le_iff_lt_or_eq.mp <| Nat.findGreatest_le _).resolve_right fun h1 =>
        (greatestDPos_is_d_pos h h0).not_le <|
          d_nonpos_of_big h <|
            (congr_arg₂ Nat.choose h1.symm rfl).le.trans' <|
              le_add_right (z 0).natAbs.choose_one_right.ge

theorem eq_greatestDPos_iff {N : ℕ} : N = greatestDPos h ↔ 0 < d z N ∧ d z (N + 1) ≤ 0 :=
  ⟨fun h1 => h1.symm ▸ ⟨greatestDPos_is_d_pos h h0, greatestDPos_succ_not_d_pos h h0⟩, fun h1 =>
    le_antisymm
      (le_of_not_lt fun h2 => h1.1.not_le <| d_nonpos_mono h (greatestDPos_succ_not_d_pos h h0) h2)
      (le_of_not_lt fun h2 => (greatestDPos_is_d_pos h h0).not_le <| d_nonpos_mono h h1.2 h2)⟩

/-! ### Final solution -/

/-- Final solution, part 1: `N` is positive. -/
theorem final_solution_part1 : 0 < greatestDPos h :=
  Nat.pos_of_ne_zero fun h1 =>
    Nat.findGreatest_eq_zero_iff.mp h1 Nat.one_pos (Nat.succ_pos _) (d_one_pos h0)

/-- Final solution, part 2: `N` is indeed the index we are looking for. -/
theorem final_solution_part2 {N : ℕ} :
    N = greatestDPos h ↔ ↑N * z N < (range (N + 1)).sum z ∧ (range (N + 1)).sum z ≤ N * z (N + 1) :=
  (eq_greatestDPos_iff h h0).trans <| and_congr sub_pos <| (d_succ z N).symm ▸ sub_nonpos

/-- Final solution, extra: `C(N, 2) < z_0`, implemented as `C(N, 2) < (z 0).nat_abs`. -/
theorem final_solution_extra : (greatestDPos h).choose 2 < (z 0).natAbs :=
  lt_of_not_le fun h1 => (d_nonpos_of_big h h1).not_lt (greatestDPos_is_d_pos h h0)
