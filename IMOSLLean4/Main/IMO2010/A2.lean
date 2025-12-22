/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev

/-!
# IMO 2010 A2

Let $R$ be a totally ordered commutative ring.
Fix some $a, b, c, d ∈ R$ such that $a + b + c + d = 6$ and $a^2 + b^2 + c^2 + d^2 = 12$.
Prove that
$$ 36 ≤ 4(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48. $$

### Solution

We follow the outline of Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2010SL.pdf),
  based on the identity $(x - 1)^4 = x^4 - 4x^3 + 6x^2 - 4x + 1$.
-/

namespace IMOSL
namespace IMO2010A2

open Finset

variable [CommRing R]

/-- The main identity `4x^3 - x^4 = 6x^2 - 4x + 1 - (x - 1)^4`. -/
theorem main_id (x : R) :
    4 * x ^ 3 - x ^ 4 = 6 * x ^ 2 - 4 * x + 1 - ((x - 1) ^ 2) ^ 2 := by
  ring

/-- The identity `(x - 1)^2 = x^2 - 2x + 1`. -/
theorem sub_one_sq (x : R) : (x - 1) ^ 2 = x ^ 2 - 2 * x + 1 := by
  rw [sub_sq, mul_one, one_pow]

/-- Summing the identity `4x^3 - x^4 = 6x^2 - 4x + 1 - (x - 1)^4` over multiple elements. -/
theorem sum_main_id (I : Finset ι) (x : ι → R) :
    4 * ∑ i ∈ I, x i ^ 3 - ∑ i ∈ I, x i ^ 4
      = 6 * ∑ i ∈ I, x i ^ 2 - 4 * ∑ i ∈ I, x i + #I - ∑ i ∈ I, ((x i - 1) ^ 2) ^ 2 :=
  calc 4 * ∑ i ∈ I, x i ^ 3 - ∑ i ∈ I, x i ^ 4
  _ = ∑ i ∈ I, (4 * x i ^ 3 - x i ^ 4) := by rw [sum_sub_distrib, mul_sum]
  _ = ∑ i ∈ I, (6 * x i ^ 2 - 4 * x i + 1 - ((x i - 1) ^ 2) ^ 2) := by simp only [main_id]
  _ = 6 * ∑ i ∈ I, x i ^ 2 - 4 * ∑ i ∈ I, x i + #I - ∑ i ∈ I, ((x i - 1) ^ 2) ^ 2 := by
    rw [sum_sub_distrib, sum_add_distrib, sum_sub_distrib,
      mul_sum, mul_sum, sum_const, nsmul_one]

/-- Summing the identity `(x - 1)^2 = x^2 - 2x + 1` over multiple elements. -/
theorem sum_sub_one_sq (I : Finset ι) (x : ι → R) :
    ∑ i ∈ I, (x i - 1) ^ 2 = ∑ i ∈ I, x i ^ 2 - 2 * ∑ i ∈ I, x i + #I :=
  calc ∑ i ∈ I, (x i - 1) ^ 2
  _ = ∑ i ∈ I, (x i ^ 2 - 2 * x i + 1) := by simp only [sub_one_sq]
  _ = ∑ i ∈ I, x i ^ 2 - 2 * ∑ i ∈ I, x i + #I := by
    rw [sum_add_distrib, sum_sub_distrib, mul_sum, sum_const, nsmul_one]


variable [LinearOrder R] [IsStrictOrderedRing R]

/-- The general bound, which generalizes the inequality to be proved. -/
theorem general_bound (I : Finset ι) (x : ι → R) :
    let B := 6 * ∑ i ∈ I, x i ^ 2 - 4 * ∑ i ∈ I, x i + #I
    let C := (∑ i ∈ I, x i ^ 2 - 2 * ∑ i ∈ I, x i + #I) ^ 2
    let L := 4 * ∑ i ∈ I, x i ^ 3 - ∑ i ∈ I, x i ^ 4
    C ≤ #I * (B - L) ∧ B - L ≤ C := by
  intro B C L
  ---- First substitute `B - L = ∑_i (x_i - 1)^4` and `C = (∑_i (x_i - 1)^2)^2`.
  have hBL : B - L = ∑ i ∈ I, ((x i - 1) ^ 2) ^ 2 := by
    dsimp only [B, L]; rw [sum_main_id, sub_sub_cancel]
  have hC : C = (∑ i ∈ I, (x i - 1) ^ 2) ^ 2 :=
    congrArg (· ^ 2) (sum_sub_one_sq I x).symm
  rw [hBL, hC]; clear * -
  ---- The two inequalities now follow by Cauchy-Schwarz and trivial bound, respectively.
  exact ⟨sq_sum_le_card_mul_sum_sq, sum_sq_le_sq_sum_of_nonneg λ _ _ ↦ sq_nonneg _⟩

/-- Final solution -/
theorem final_solution {I : Finset ι} (hI : #I = 4) {x : ι → R}
    (hxI1 : ∑ i ∈ I, x i = 6) (hxI2 : ∑ i ∈ I, x i ^ 2 = 12) :
    let L := 4 * ∑ i ∈ I, x i ^ 3 - ∑ i ∈ I, x i ^ 4
    36 ≤ L ∧ L ≤ 48 := by
  intro L
  ---- In this case we have `B = 52` and `C = 16`, so `16 ≤ 4(52 - L)` and `52 - L ≤ 16`.
  have hB : 6 * ∑ i ∈ I, x i ^ 2 - 4 * ∑ i ∈ I, x i + #I = 52 := by
    rw [hxI1, hxI2, hI]; norm_num
  have hC : (∑ i ∈ I, x i ^ 2 - 2 * ∑ i ∈ I, x i + #I) ^ 2 = 4 * 4 := by
    rw [hxI1, hxI2, hI]; norm_num
  obtain ⟨h, h0⟩ : 4 * 4 ≤ ((4 : ℕ) : R) * (52 - L) ∧ 52 - L ≤ 4 * 4 := by
    rw [← hI, ← hB, ← hC]; exact general_bound I x
  ---- Now we just deduce the inequality we want.
  clear * - h h0
  refine ⟨?_, ?_⟩
  ---- First prove `L ≥ 36`.
  · calc (36 : R) = 52 - 4 * 4 := by norm_num
                _ ≤ L := sub_le_comm.mp h0
  ---- Now prove `L ≤ 48`.
  · replace h : 4 ≤ 52 - L := le_of_mul_le_mul_left (a := 4) h four_pos
    calc  L ≤ 52 - 4 := le_sub_comm.mp h
          _ = 48 := by norm_num
