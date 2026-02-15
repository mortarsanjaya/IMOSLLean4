/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# IMO 2007 A6

Let $R$ be a totally ordered commutative ring.
Let $n ≥ 5$ be a positive integer, and let $a_1, a_2, …, a_n ∈ R$
  be elements such that $a_1^2 + a_2^2 + … + a_n^2 = 1$.
Prove that $25 \sum_{i = 1}^n a_i^2 a_{i + 1} < 12$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2007SL.pdf).
In particular, we prove an even more general inequality:
$$ \left(3 \sum_{i = 1}^n a_i^2 a_{i + 1}\right)^2 ≤ 2 \left(\sum_{i = 1}^n a_i^2\right)^3. $$
However, one hole in an attempt to do the estimation in general is that the inequality
$$ 4 \sum_{i = 1}^n x_i x_{i + 1} ≤ \left(\sum_{i = 1}^n x_i\right)^2 $$
  for $x_1, …, x_n ≥ 0$ is nontrivial for odd $n$.
(This estimate correspond to the second "trivial" estimate in the official solution,
  although they are not directly the same for $n = 100$.)
We prove the above inequality for all $n ≥ 4$ by induction on $n$.
The base case $n = 4$ reads as
$$ 4(x_1 + x_3)(x_2 + x_4) ≤ (x_1 + x_3 + x_2 + x_4)^2, $$
  which follows by the AM-GM inequality.

For the induction step, let $n ≥ 4$ and consider $x_1, …, x_{n + 1} ∈ R$ non-negative.
We first claim that there exists an index $i₀$ such that
$$ 2 ∑_{i = 1}^n x_i ≥ 4(x_{i₀ - 1} + x_{i₀ + 1}) + x_{i₀}. $$
Indeed, if the sign above is $<$ for all $i₀$, then summing over all $i₀$ yields
$$ 2(n + 1) ∑_i x_i < 9 ∑_i x_i, $$
  which contradicts $n ≥ 4$.
This proves the claim.

Now we may assume, without loss of generality, that $i₀ = 1$.
For convenience, write $y_i = x_{i + 1}$ for each $i = 1, 2, …, n$ and $y_{n + 1} = y_1$.
Then we have
\begin{align*}
  4 \sum_{i = 1}^{n + 1} x_i x_{i + 1}
  &≤ 4 \sum_{i = 1}^{n + 1} x_i x_{i + 1} + x_{n + 1} x_2
  &= 4 \sum_{i = 1}^n y_i y_{i + 1} + 4x_1 (x_n + x_2)
  &≤ \left(\sum_{i = 1}^n y_i\right)^2 + x_1 \left(2 \sum_{i ≠ 1} x_i + x_0\right)
  &= \left(\sum_{i = 1}^{n + 1} x_i\right)^2,
\end{align*}
  as desired.

In the implementation, we assume the smallest value among the $x_i$'s is $x_0$ instead.
-/

namespace IMOSL
namespace IMO2007A6

open Finset

/-- We have `∑_i a_{k + i} = ∑_i a_i`, where the summation runs over `Fin n`. -/
theorem Fin_sum_add_left [NeZero n] [AddCommMonoid M] (a : Fin n → M) (k) :
    ∑ i, a (k + i) = ∑ i, a i :=
  Fintype.sum_equiv (Equiv.addLeft k) _ _ (λ _ ↦ rfl)

/-- We have `∑_i a_{i + k} = ∑_i a_i`, where the summation runs over `Fin n`. -/
theorem Fin_sum_add_right [NeZero n] [AddCommMonoid M] (a : Fin n → M) (k) :
    ∑ i, a (i + k) = ∑ i, a i :=
  Fintype.sum_equiv (Equiv.addRight k) _ _ (λ _ ↦ rfl)

open Fin.NatCast in
/-- Taking `Fin.castLE` is the same as casting the value into the higher `Fin`. -/
theorem Fin_castLE_eq_natCast_val [NeZero m] (h : n ≤ m) (i : Fin n) :
    i.castLE h = i.val := by
  rw [Fin.ext_iff, Fin.val_castLE, Fin.val_natCast, Nat.mod_eq_of_lt (i.2.trans_le h)]

open Fin.NatCast in
/-- The identity
  `∑_i (x_i^2 + 2 x_i (x_{i + 1} + x_{i + 2})) = ∑_i x_{i + 2} ∑_{j < 5} x_{i + j}`. -/
theorem main_identity [CommSemiring R] [NeZero n] (hn : n ≥ 5) (x : Fin n → R) :
    ∑ i, (x i ^ 2 + 2 * x i * (x (i + 1) + x (i + 1 + 1)))
      = ∑ i, x (i + 2) * ∑ j : Fin 5, x (i + j.castLE hn) := by
  ---- Rearrange appropriately.
  calc ∑ i, (x i ^ 2 + 2 * x i * (x (i + 1) + x (i + 1 + 1)))
    _ = ∑ i, (x i ^ 2 + 2 * x i * (x (i + 1) + x (i + 2))) := by
      conv_lhs => right; ext i; rw [add_assoc, one_add_one_eq_two]
    _ = ∑ i, (x (i + 2) * x i + x (i + 1) * x i + x i * x i
        + x i * x (i + 1) + x i * x (i + 2)) :=
      Fintype.sum_congr _ _ λ _ ↦ by ring
    _ = ∑ i, x (i + 2) * x i + ∑ i, x (i + 1) * x i + ∑ i, x i * x i
        + ∑ i, x i * x (i + 1) + ∑ i, x i * x (i + 2) := by
      iterate 4 rw [sum_add_distrib]
    _ = ∑ i, x (i + 2) * x (i + 0) + ∑ i, x (i + 2) * x (i + 1) + ∑ i, x (i + 2) * x (i + 2)
        + ∑ i, x (i + 2) * x (i + 3) + ∑ i, x (i + 2) * x (i + 4) := ?_
    _ = ∑ i, x (i + 2) * x (i + Fin.castLE hn 0)
        + ∑ i, x (i + 2) * x (i + Fin.castLE hn 1)
        + ∑ i, x (i + 2) * x (i + Fin.castLE hn 2)
        + ∑ i, x (i + 2) * x (i + Fin.castLE hn 3)
        + ∑ i, x (i + 2) * x (i + Fin.castLE hn 4) := by
      simp only [Fin_castLE_eq_natCast_val]; rfl
    _ = ∑ i, x (i + 2) * ∑ j : Fin 5, x (i + j.castLE hn) := by
      simp_rw [Fin.sum_univ_five, mul_add, sum_add_distrib]
  ---- Now equate term-by-term.
  refine congrArg₂ _ (congrArg₂ _ (congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_) ?_) ?_
  ---- Term `0`: `∑_i x_{i + 2} x_i = ∑_i x_{i + 2} x_{i + 0}`.
  · simp only [add_zero]
  ---- Term `1`: `∑_i x_{i + 1} x_i = ∑_i x_{i + 2} x_{i + 1}`.
  · calc ∑ i, x (i + 1) * x i
      _ = ∑ i, x (i + 1 + 1) * x (i + 1) := (Fin_sum_add_right _ 1).symm
      _ = ∑ i, x (i + 2) * x (i + 1) := by simp_rw [add_assoc, one_add_one_eq_two]
  ---- Term `2`: `∑_i x_i x_i = ∑_i x_{i + 2} x_{i + 2}`.
  · exact (Fin_sum_add_right _ 2).symm
  ---- Term `3`: `∑_i x_i x_{i + 1} = ∑_i x_{i + 2} x_{i + 3}`.
  · calc ∑ i, x i * x (i + 1)
      _ = ∑ i, x (i + 2) * x (i + 2 + 1) := (Fin_sum_add_right _ 2).symm
      _ = ∑ i, x (i + 2) * x (i + 3) := by simp_rw [add_assoc, two_add_one_eq_three]
  ---- Term `4`: `∑_i x_i x_{i + 2} = ∑_i x_{i + 2} x_{i + 4}`.
  · calc ∑ i, x i * x (i + 2)
      _ = ∑ i, x (i + 2) * x (i + 2 + 2) := (Fin_sum_add_right _ 2).symm
      _ = ∑ i, x (i + 2) * x (i + 4) := by simp_rw [add_assoc, two_add_two_eq_four]

/-- The identity `∑_i x_i x_{i + 1} + x_n x_1 = ∑_i y_i y_{i + 1} + x_0 (x_n + x_1)`;
  LHS sum is over `Fin (n + 1)` and `y : Fin n → R` is defined by `y_i = x_{i + 1}`. -/
theorem main_ineq_identity [CommSemiring R] [hn : NeZero n] (x : Fin (n + 1) → R) :
    ∑ i, x i * x (i + 1) + x (Fin.last n) * x 1
      = ∑ i : Fin n, x i.succ * x (i + 1).succ + x 0 * (x (Fin.last n) + x 1) := by
  cases n with | zero => exact absurd rfl (NeZero.ne 0) | succ n => ?_
  calc ∑ i, x i * x (i + 1) + x (Fin.last (n + 1)) * x 1
    _ = x 0 * x 1 + (∑ i : Fin n, x i.castSucc.succ * x (i.castSucc.succ + 1)
        + x (Fin.last n.succ) * x 0) + x (Fin.last (n + 1)) * x 1 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc,
        zero_add, Fin.succ_last, Fin.last_add_one]
    _ = ∑ i : Fin n, x i.castSucc.succ * x (i.castSucc.succ + 1)
        + (x (Fin.last (n + 1)) * x 1) + x 0 * (x (Fin.last (n + 1)) + x 1) := by
      rw [add_rotate', mul_comm _ (x 0), ← mul_add, add_right_comm]
    _ = ∑ i : Fin (n + 1), x i.succ * x (i + 1).succ
        + x 0 * (x (Fin.last (n + 1)) + x 1) := by
      rw [Fin.sum_univ_castSucc, Fin.last_add_one, Fin.succ_zero_eq_one, Fin.succ_last]
      simp_rw [Fin.succ_castSucc, Fin.coeSucc_eq_succ]

/-- If `n ≥ 5` and `x_0, x_1, …, x_{n - 1} ≥ 0`, then for any indices `j₁, j₂`, there exists
  an index `i₀` such that `x_{i₀} + 2 ∑_{i ≠ i₀} x_i ≥ 4(x_{i₀ + j₁} + x_{i₀ + j₂})`. -/
theorem exists_index_special
    [AddCommMonoid G] [LinearOrder G] [IsOrderedCancelAddMonoid G] [AddLeftStrictMono G]
    (hn : n ≥ 5) {x : Fin n → G} (hx : ∀ i, 0 ≤ x i) (j₁ j₂) :
    ∃ i₀, 4 • (x (i₀ + j₁) + x (i₀ + j₂)) ≤ x i₀ + 2 • ∑ i ∈ {i₀}ᶜ, x i := by
  haveI : NeZero n := NeZero.of_gt hn
  ---- If not, summing over all `i₀` yields contradiction.
  by_contra! hx0
  suffices (2 * n) • ∑ i, x i < 9 • ∑ i, x i
    from this.not_ge <| nsmul_le_nsmul_left (sum_nonneg' hx)
      (Nat.le_of_lt (Nat.mul_le_mul_left 2 hn))
  calc (2 * n) • ∑ i, x i
    _ = ∑ _ : Fin n, 2 • ∑ i, x i := by rw [sum_const, card_fin, mul_nsmul]
    _ = ∑ i₀, (x i₀ + 2 • ∑ i ∈ {i₀}ᶜ, x i + x i₀) := by
      refine Fintype.sum_congr _ _ λ i₀ ↦ ?_
      rw [add_right_comm, ← two_nsmul, ← nsmul_add, ← Fintype.sum_eq_add_sum_compl]
    _ = ∑ i₀, (x i₀ + 2 • ∑ i ∈ {i₀}ᶜ, x i) + ∑ i, x i := sum_add_distrib
    _ < ∑ i₀, 4 • (x (i₀ + j₁) + x (i₀ + j₂)) + ∑ i, x i :=
      add_lt_add_left (sum_lt_sum_of_nonempty univ_nonempty λ i _ ↦ hx0 i) _
    _ = 4 • (∑ i, x i + ∑ i, x i) + ∑ i, x i := by
      rw [sum_nsmul, sum_add_distrib, Fin_sum_add_right, Fin_sum_add_right]
    _ = 9 • ∑ i, x i := by rw [← two_nsmul, ← mul_nsmul, ← succ_nsmul]


variable {R} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

/-- The inequality `4 ∑_i x_i x_{i + 1} ≤ (∑_i x_i)^2` over `Fin 4`. -/
theorem main_ineq_Fin4 (x : Fin 4 → R) : 4 * ∑ i, x i * x (i + 1) ≤ (∑ i, x i) ^ 2 := by
  calc 4 * ∑ i, x i * x (i + 1)
    _ = 4 * (x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 3 * x 0) :=
      congrArg (4 * ·) (Fin.sum_univ_four _)
    _ = 4 * (x 0 + x 2) * (x 1 + x 3) := by
      rw [mul_comm (x 1), ← add_mul, add_assoc, mul_comm (x 3),
        ← add_mul, add_comm (x 2), ← mul_add, mul_assoc]
    _ ≤ (x 0 + x 2 + (x 1 + x 3)) ^ 2 := four_mul_le_pow_two_add _ _
    _ ≤ (∑ i, x i) ^ 2 := by rw [Fin.sum_univ_four, add_add_add_comm, ← add_assoc]

/-- The inequality `4 ∑_i x_i x_{i + 1} ≤ (∑_i x_i)^2`. -/
theorem main_ineq [hn : NeZero n] (hn0 : n ≥ 4) {x : Fin n → R} (hx : ∀ i, 0 ≤ x i) :
    4 * ∑ i, x i * x (i + 1) ≤ (∑ i, x i) ^ 2 := by
  ---- Induction on n `n`; the base case `n = 4` is proved in `main_ineq_Fin4`.
  induction n, hn0 using Nat.le_induction generalizing hn with
  | base => exact main_ineq_Fin4 x
  | succ n hn0 n_ih => ?_
  ---- WLOG we may assume `x_0 + 2 ∑_{i ≠ 0} x_i ≥ 4(x_n + x_1)`.
  wlog h : 4 • (x (Fin.last n) + x 1) ≤ x 0 + 2 • ∑ i ∈ {0}ᶜ, x i generalizing x
  · -- Indeed, there is `iₐ` with `x_{i₀} + 2 ∑_{i ≠ i₀} x_i ≥ 4(x_{i₀ - 1} + x_{i₀ + 1})`.
    obtain ⟨i₀, hi₀⟩ :
        ∃ i₀, 4 • (x (i₀ + Fin.last n) + x (i₀ + 1)) ≤ x i₀ + 2 • ∑ i ∈ {i₀}ᶜ, x i :=
      exists_index_special (Nat.succ_le_succ hn0) hx _ _
    -- We just need to shift `i₀` to `0`.
    calc 4 * ∑ i, x i * x (i + 1)
      _ = 4 * ∑ i, x (i₀ + i) * x (i₀ + i + 1) :=
        congrArg (4 * ·) (Fin_sum_add_left _ _).symm
      _ = 4 * ∑ i, x (i₀ + i) * x (i₀ + (i + 1)) := by simp only [add_assoc]
      _ ≤ (∑ i, x (i₀ + i)) ^ 2 := by
        refine this (λ _ ↦ hx _) <| hi₀.trans_eq <| congrArg₂ (x · + 2 • ·)
          (add_zero _).symm (sum_equiv (Equiv.addLeft i₀) (λ i ↦ ?_) (λ _ _ ↦ rfl)).symm
        rw [mem_compl, mem_singleton, mem_compl,
          mem_singleton, Equiv.coe_addLeft, add_eq_left]
      _ = (∑ i, x i) ^ 2 := congrArg (· ^ 2) (Fin_sum_add_left _ _)
  ---- We only need the induction hypothesis on the `x_i`s with `x_0` removed.
  have hn1 : NeZero n := NeZero.of_gt hn0
  specialize n_ih (x := λ i ↦ x i.succ) (λ _ ↦ hx _)
  ---- Now do the calculations.
  calc 4 * ∑ i, x i * x (i + 1)
    _ ≤ 4 * (∑ i, x i * x (i + 1) + x (Fin.last n) * x 1) :=
      mul_le_mul_of_nonneg_left (ha := zero_le_four)
        (le_add_of_nonneg_right (mul_nonneg (hx _) (hx _)))
    _ = 4 * ∑ i : Fin n, x i.succ * x (i + 1).succ + x 0 * 4 • (x (Fin.last n) + x 1) := by
      rw [main_ineq_identity, mul_add, nsmul_eq_mul, mul_left_comm, Nat.cast_four]
    _ ≤ (∑ i : Fin n, x i.succ) ^ 2 + x 0 * (x 0 + 2 • ∑ i ∈ {0}ᶜ, x i) :=
      add_le_add n_ih (mul_le_mul_of_nonneg_left h (hx _))
    _ = (∑ i, x i) ^ 2 := by
      rw [← Fin.image_succ_univ, sum_image (Set.injOn_of_injective (Fin.succ_injective n)),
        mul_add, ← sq, ← add_assoc, nsmul_eq_mul, Nat.cast_two, mul_comm, ← add_sq',
        add_comm, ← Fin.sum_univ_succ]

/-- The general result `(3 ∑_i a_i^2 a_{i + 1})^2 ≤ 2 (∑_i a_i^2)^3`. -/
theorem general_result [NeZero n] (hn : n ≥ 5) (a : Fin n → R) :
    (3 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2 ≤ 2 * (∑ i, a i ^ 2) ^ 3 := by
  /- Prove `(3 ∑_i a_i^2 a_{i + 1})^2 ≤ (∑_i a_i^2)(∑_i (a_i^2 + 2 a_{i + 1} a_{i + 2})^2)`.
    Thus we only need to prove `∑_i (a_i^2 + 2 a_{i + 1} a_{i + 2})^2 ≤ 2 (∑_i a_i^2)^2`. -/
  calc (3 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2
    _ = (∑ i, (a i ^ 2 * a (i + 1) + 2 * (a (i + 1) ^ 2 * a (i + 1 + 1)))) ^ 2 := by
      rw [sum_add_distrib, ← mul_sum, Fin_sum_add_right (λ i ↦ a i ^ 2 * a (i + 1)),
        add_comm, ← add_one_mul, two_add_one_eq_three]
    _ = (∑ i, a (i + 1) * (a i ^ 2 + 2 * a (i + 1) * a (i + 1 + 1))) ^ 2 :=
      congrArg (· ^ 2) (Fintype.sum_congr _ _ λ i ↦ by ring)
    _ ≤ (∑ i, a (i + 1) ^ 2) * (∑ i, (a i ^ 2 + 2 * a (i + 1) * a (i + 1 + 1)) ^ 2) :=
      sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ i, a (i + 1) ^ 2) * (2 * (∑ i, a i ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left ?_ (Fintype.sum_nonneg λ _ ↦ sq_nonneg _)
    _ = 2 * (∑ i, a i ^ 2) ^ 3 := by
      rw [Fin_sum_add_right (λ i ↦ a i ^ 2), mul_left_comm, ← pow_succ']
  /- Now break up LHS into `∑_i (a_i^4 + 4 a_i^2 a_{i + 1} a_{i + 2})` and
    `4 ∑_{i + 1} a_i^2 a_{i + 1}^2 ≤ (∑_i a_i^2)^2`, so it remains to show that
    `∑_i (a_i^4 + 4 a_i^2 a_{i + 1} a_{i + 2}) ≤ (∑_i a_i^2)^2`. -/
  calc ∑ i, (a i ^ 2 + 2 * a (i + 1) * a (i + 1 + 1)) ^ 2
    _ = ∑ i, ((a i ^ 2) ^ 2 + 2 * a i ^ 2 * (2 * a (i + 1) * a (i + 1 + 1))
        + 4 * (a (i + 1) ^ 2 * a (i + 1 + 1) ^ 2)) :=
      Fintype.sum_congr _ _ λ _ ↦ by ring
    _ = ∑ i, ((a i ^ 2) ^ 2 + 2 * a i ^ 2 * (2 * a (i + 1) * a (i + 1 + 1)))
        + 4 * ∑ i, a i ^ 2 * a (i + 1) ^ 2 := by
      rw [sum_add_distrib, ← mul_sum, Fin_sum_add_right (λ i ↦ a i ^ 2 * a (i + 1) ^ 2)]
    _ ≤ (∑ i, a i ^ 2) ^ 2 + (∑ i, a i ^ 2) ^ 2 :=
      add_le_add ?_ (main_ineq (Nat.le_of_lt hn) (λ _ ↦ sq_nonneg _))
    _ = 2 * (∑ i, a i ^ 2) ^ 2 := (two_mul _).symm
  /- Finally, prove `∑_i (a_i^4 + 4 a_i^2 a_{i + 1} a_{i + 2}) ≤ (∑_i a_i^2)^2`. -/
  calc ∑ i, ((a i ^ 2) ^ 2 + 2 * a i ^ 2 * (2 * a (i + 1) * a (i + 1 + 1)))
    _ ≤ ∑ i, ((a i ^ 2) ^ 2 + 2 * a i ^ 2 * (a (i + 1) ^ 2 + a (i + 1 + 1) ^ 2)) :=
      sum_le_sum λ i _ ↦ add_le_add_right (a := (a i ^ 2) ^ 2) <|
        mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _)
          (mul_nonneg zero_le_two (sq_nonneg _))
    _ = ∑ i, a (i + 2) ^ 2 * ∑ j : Fin 5, a (i + j.castLE hn) ^ 2 :=
      main_identity hn _
    _ = ∑ i, a (i + 2) ^ 2 * ∑ j ∈ image (Fin.castLE hn) univ, a (i + j) ^ 2 :=
      Fintype.sum_congr _ _ λ i ↦ congrArg (_ * ·)
        (sum_image (f := λ j ↦ a (i + j) ^ 2)
          (Set.injOn_of_injective (Fin.castLE_injective hn))).symm
    _ ≤ ∑ i, a (i + 2) ^ 2 * ∑ j, a (i + j) ^ 2 :=
      sum_le_sum λ _ _ ↦ mul_le_mul_of_nonneg_left
        (sum_le_univ_sum_of_nonneg λ _ ↦ sq_nonneg _) (sq_nonneg _)
    _ = ∑ i, a (i + 2) ^ 2 * ∑ j, a j ^ 2 :=
      Fintype.sum_congr _ _ λ i ↦ congrArg (_ * ·) (Fin_sum_add_left (λ j ↦ a j ^ 2) i)
    _ = (∑ i, a i ^ 2) ^ 2 := by
      rw [Fin_sum_add_right (λ i ↦ a i ^ 2 * ∑ j, a j ^ 2), sq, sum_mul]

/-- Final solution -/
theorem final_solution [NeZero n] (hn : n ≥ 5) {a : Fin n → R} (ha : ∑ i, a i ^ 2 = 1) :
    25 * ∑ i, a i ^ 2 * a (i + 1) < 12 := by
  refine lt_of_pow_lt_pow_left₀ 2 (Nat.ofNat_nonneg 12) ?_
  calc (25 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2
    _ = 25 ^ 2 * (∑ i, a i ^ 2 * a (i + 1)) ^ 2 := mul_pow _ _ _
    _ ≤ 70 * 3 ^ 2 * (∑ i, a i ^ 2 * a (i + 1)) ^ 2 := by
      have h : (25 ^ 2 : R) ≤ 70 * 3 ^ 2 := calc
        _ ≤ (25 ^ 2 : R) + 5 := le_add_of_nonneg_right (Nat.ofNat_nonneg 5)
        _ = 70 * 3 ^ 2 := by norm_num
      exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = 70 * (3 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2 := by rw [mul_assoc, mul_pow]
    _ ≤ 70 * (2 * (∑ i, a i ^ 2) ^ 3) :=
      mul_le_mul_of_nonneg_left (general_result hn a) (Nat.ofNat_nonneg 70)
    _ = 70 * 2 := by rw [ha, one_pow, mul_one]
    _ < 70 * 2 + 4 := lt_add_of_pos_right _ four_pos
    _ = 12 ^ 2 := by norm_num
