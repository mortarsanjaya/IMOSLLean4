/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-
# IMO 2024 A3

Let $(a_n)_{n ≥ 0}$ be a sequence of positive real numbers.
Does there exist $n > 0$ such that
$$ \frac{3^{a_1} + 3^{a_2} + … + 3^{a_n}}{(2^{a_1} + 2^{a_2} + … + 2^{a_n})^2}
  < \frac{1}{2024}? $$

### Answer

Yes, with $\dfrac{1}{2024}$ replaced by any positive real number.
In fact, any $n$ large enough works, independent of the sequence,
  and the sequence may take the value $0$.
This generalized statement is the one we implement.

### Solution

We follow the [solution](https://artofproblemsolving.com/community/c6h3610463p35341002)
  in the AoPS thread post #3 by **OronSH**.
It is based on the inequality $(x_1 + x_2)^y ≥ x_1^y + x_2^y$ for $x_1, x_2 ≥ 0$, $y ≥ 1$.
-/

namespace IMOSL
namespace IMO2024A3

open Finset NNReal

/-- Given real numbers `x_1, x_2, …, x_n ≥ 0` and `p ≥ 1`,
  we have `x_1^p + x_2^p + … + x_n^p ≤ (x_1 + x_2 + … + x_n)^p`. -/
theorem Finset_sum_rpow_le_rpow_sum {p : ℝ} (hp : 1 ≤ p) (I : Finset ι) (x : ι → ℝ≥0) :
    ∑ i ∈ I, x i ^ p ≤ (∑ i ∈ I, x i) ^ p :=
  have hp0 : p - 1 + 1 = p := sub_add_cancel p 1
  have hp1 : p - 1 + 1 ≠ 0 := hp0.trans_ne (one_pos.trans_le hp).ne.symm
  calc ∑ i ∈ I, x i ^ p
    _ = ∑ i ∈ I, x i ^ (p - 1) * x i :=
      sum_congr rfl λ i _ ↦ by rw [← rpow_add_one' hp1, hp0]
    _ ≤ ∑ i ∈ I, (∑ j ∈ I, x j) ^ (p - 1) * x i := by
      -- This follows from the trivial bound `f(i) ≤ ∑ j, f(j)`.
      refine sum_le_sum λ i hi ↦ mul_le_mul_left ?_ _
      exact rpow_le_rpow (single_le_sum_of_canonicallyOrdered hi) (sub_nonneg_of_le hp)
    _ = (∑ i ∈ I, x i) ^ p := by rw [← mul_sum, ← rpow_add_one' hp1, hp0]

/-- Given real numbers `p` and `q` with `1 ≤ q < p` and `ε > 0`, there exists an
  integer `N` such that for any `n ≥ N` real numbers `x_1, x_2, …, x_n ≥ 1`,
  we have `x_1^q + x_2^q + … + x_n^q < ε(x_1 + x_2 + … + x_n)^p`. -/
theorem exists_N_forall_target_lt_eps_of_card_ge_N.{u}
    {p q : ℝ} (hq : 1 ≤ q) (hqp : q < p) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ N, ∀ (ι : Type u) (_ : DecidableEq ι) (I : Finset ι) (_ : #I ≥ N)
      (x : ι → ℝ≥0) (_ : ∀ i ∈ I, 1 ≤ x i),
        (∑ i ∈ I, x i ^ q) / (∑ i ∈ I, x i) ^ p < ε := by
  replace hqp : q - p < 0 := sub_neg.mpr hqp
  ---- Looking into the future, we first find `N > 0` such that `N^{q - p} < ε`.
  obtain ⟨N, hN, hN0⟩ : ∃ N : ℕ, 0 < (N : ℝ≥0) ∧ (N : ℝ≥0) ^ (q - p) < ε := by
    -- Pick any `N` such that `N > ε^{1/(q - p)}`.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ε ^ ((q - p)⁻¹) < N := exists_nat_gt _
    -- This `N` is positive and, since `q - p < 0`, it satisfies `N^{q - p} < ε`.
    refine ⟨N, hN.trans_le' (Subtype.property _), ?_⟩
    calc (N : ℝ≥0) ^ (q - p)
      _ < (ε ^ ((q - p)⁻¹)) ^ (q - p) := rpow_lt_rpow_of_neg (rpow_pos hε) hN hqp
      _ = ε := by rw [← rpow_mul, inv_mul_cancel₀ hqp.ne, rpow_one]
  ---- Now we claim that this `N` works.
  refine ⟨N, λ i _ I hI x hx ↦ ?_⟩
  ---- Do the calculation to show that the above `N` works.
  calc (∑ i ∈ I, x i ^ q) / (∑ i ∈ I, x i) ^ p
    _ ≤ (∑ i ∈ I, x i) ^ q / (∑ i ∈ I, x i) ^ p :=
      div_le_div_of_nonneg_right (Finset_sum_rpow_le_rpow_sum hq I x) (Subtype.property _)
    _ = (∑ i ∈ I, x i) ^ (q - p) := (rpow_sub' hqp.ne _).symm
    _ ≤ N ^ (q - p) := rpow_le_rpow_of_nonpos hN ?_ hqp.le
    _ < ε := hN0
  ---- We're left to show that `N ≤ ∑_i x_i`.
  calc (N : ℝ≥0)
    _ ≤ #I := Nat.cast_le.mpr hI
    _ = #I • (1 : ℝ≥0) := (nsmul_one _).symm
    _ ≤ ∑ i ∈ I, x i := card_nsmul_le_sum I x 1 hx

/-- Final solution -/
theorem final_solution {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a : ℕ → ℝ≥0, ∀ n ≥ N,
      (∑ i ∈ range n, (3 : ℝ≥0) ^ (a i : ℝ))
        / (∑ i ∈ range n, 2 ^ (a i : ℝ)) ^ (2 : ℝ) < ε := by
  ---- First collect some facts about `Real.logb 2 3`.
  have X0lt3 : (0 : ℝ) < 3 := three_pos
  have X1lt2 : (1 : ℝ) < 2 := one_lt_two
  have X2powq : (2 : ℝ≥0) ^ Real.logb 2 3 = 3 :=
    Subtype.coe_injective (Real.rpow_logb two_pos X1lt2.ne.symm X0lt3)
  have X1leq : 1 ≤ Real.logb 2 3 :=
    (Real.le_logb_iff_rpow_le X1lt2 X0lt3).mpr (by norm_num)
  have Xqle2 : Real.logb 2 3 < 2 :=
    (Real.logb_lt_iff_lt_rpow X1lt2 X0lt3).mpr (by norm_num)
  ---- Find some `N` according to `exists_N_forall_target_lt_eps_of_card_ge_N`.
  obtain ⟨N, hN⟩ := exists_N_forall_target_lt_eps_of_card_ge_N.{0} X1leq Xqle2 hε
  ---- Now we claim that this `N` works.
  refine ⟨N, λ a n hn ↦ ?_⟩
  ---- Do the calculation to show that the above `N` works.
  calc (∑ i ∈ range n, (3 : ℝ≥0) ^ (a i : ℝ)) / (∑ i ∈ range n, 2 ^ (a i : ℝ)) ^ (2 : ℝ)
    _ = (∑ i ∈ range n, ((2 : ℝ≥0) ^ (a i : ℝ)) ^ Real.logb 2 3)
        / (∑ i ∈ range n, (2 : ℝ≥0) ^ (a i : ℝ)) ^ (2 : ℝ) := by
      refine congrArg (· / _) (sum_congr rfl λ i _ ↦ ?_)
      rw [← X2powq, ← rpow_mul, mul_comm, rpow_mul]
    _ < ε :=
      hN ℕ instDecidableEqNat _ (hn.trans_eq (card_range n).symm)
        _ (λ i _ ↦ one_le_rpow X1lt2.le (a i).2)
