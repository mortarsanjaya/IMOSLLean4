/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int

/-!
# IMO 2008 N1

Let $m, n, p$ be non-negative integers with $m$ odd and $p$ prime.
Let $x_1, x_2, …, x_m$ be integers such that
$$ x_1^n + px_2 = x_2^n + px_3 = … = x_m^n + px_1. $$
Prove that $x_1 = x_2 = … = x_n$.

### Solution

We follow Solution 2 of the
  [official solution](https://www.imo-official.org/problems/IMO2008SL.pdf),
  with some shortcuts made along the way.
For $n$ odd, we show that $x_i < x_{i + 2}$ implies $x_{i + 2} < x_{i + 4}$,
  and similarly $x_i > x_{i + 2}$ implies $x_{i + 2} > x_{i + 4}$.
In particular, $p$ only needs to either be odd or equal to $±2$;
  the above modification makes sure that the solution works even when $p < 0$.
Our implementation will also assume $p$ is either odd or $±2$ instead of being prime.
For the case $p = ±2$, $n = 2k$, after showing $|x_i^k + x_{i + 1}^k| = 2$,
  we deduce $x_{i + 1}^k = x_{i - 1}^k$ for some $i$ and then get $x_{i + 2} = x_i$.

### Notes

The original problem considers $m = 3$, but the same method works for any odd $m$.
However, the statement is false when $p = 4$ and $m = 3$.
A counterexample is given by $(x_1, x_2, x_3) = (7, -5, 1)$ with $n = 2$.
-/

namespace IMOSL
namespace IMO2008N1

open Fin.NatCast

/-! ### Extra lemmas -/

/-- If `a ∣ b` and `b` is odd, then `a` is odd. -/
theorem odd_of_dvd_Int {a b : ℤ} (ha : Odd b) (hab : a ∣ b) : Odd a := by
  rcases hab with ⟨c, rfl⟩
  exact Int.Odd.of_mul_left ha

/-- Given natural numbers `m` and `n`, we have `mn = 1` iff `m = 1` and `n = 1`. -/
theorem mul_eq_one_Nat : m * n = 1 ↔ m = 1 ∧ n = 1 :=
  ⟨λ h ↦ ⟨Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h⟩,
  λ ⟨h, h0⟩ ↦ congrArg₂ Nat.mul h h0⟩


section

open Finset

variable [DecidableEq ι]

/-- The product of several integers is odd iff each term is odd. -/
theorem odd_prod_Int {f : ι → ℤ} {I : Finset ι} :
    Odd (∏ i ∈ I, f i) ↔ ∀ i ∈ I, Odd (f i) := by
  induction I using Finset.induction with
  | empty => rw [forall_mem_empty_iff, iff_true]; exact odd_one
  | insert i₀ I hi₀ hI =>
      rw [prod_insert hi₀, Int.odd_mul, forall_mem_insert]
      exact and_congr_right' hI

/-- The product of several integers is odd iff each term is odd. -/
theorem odd_prod_Int_Fintype [Fintype ι] {f : ι → ℤ} :
    Odd (∏ i, f i) ↔ ∀ i, Odd (f i) := by
  simp_rw [odd_prod_Int, mem_univ, forall_const]

/-- If the product of several natural numbers is one, then each term is one. -/
theorem prod_eq_one_Nat {f : ι → ℕ} {I : Finset ι} :
    ∏ i ∈ I, f i = 1 ↔ ∀ i ∈ I, f i = 1 := by
  induction I using Finset.induction with
  | empty => rw [forall_mem_empty_iff, iff_true, prod_empty]
  | insert i₀ I hi₀ hI =>
      rw [prod_insert hi₀, mul_eq_one_Nat, forall_mem_insert]
      exact and_congr_right' hI

/-- If the product of several natural numbers is one, then each term is one. -/
theorem prod_eq_one_Nat_Fintype [Fintype ι] {f : ι → ℕ} :
    ∏ i, f i = 1 ↔ ∀ i, f i = 1 := by
  simp_rw [prod_eq_one_Nat, mem_univ, forall_const]

/-- The `natAbs` of product is equal to the product of `natAbs`. -/
theorem natAbs_prod_Int (f : ι → ℤ) (I : Finset ι) :
    (∏ i ∈ I, f i).natAbs = ∏ i ∈ I, (f i).natAbs := by
  induction I using Finset.induction with
  | empty => rfl
  | insert i₀ I hi₀ hI => rw [prod_insert hi₀, prod_insert hi₀, Int.natAbs_mul, hI]

end





/-! ### Start of the problem -/

/-- A sequence `x_1, x_2, …, x_m` of integers is called `(n, p)`-**good**
  if `x_i^n + px_{i + 1} = x_j^n + px_{j + 1}` holds for any `i : ℕ`. -/
def good (m n : ℕ) (p : ℤ) [NeZero m] (x : Fin m → ℤ) :=
  ∀ i j, x i ^ n + p * x (i + 1) = x j ^ n + p * x (j + 1)


namespace good

variable {m : ℕ} [NeZero m]


section

variable {n : ℕ} {p : ℤ} (hp : p ≠ 0) {x : Fin m → ℤ} (hx : good m n p x)
include hp hx

/-- Suppose `p ≠ 0`, and let `(x_i)` be an `(n, p)`-good sequence.
  If `x_i = x_j`, then `x_{i + k} = x_{j + k}` for any `k`. -/
theorem map_add_eq_of_map_eq (hx0 : x i = x j) (k) : x (i + k) = x (j + k) := by
  have h {i j} (h : x i = x j) : x (i + 1) = x (j + 1) := by
    specialize hx i j
    rwa [h, Int.add_right_inj, Int.mul_eq_mul_left_iff hp] at hx
  replace h (k : ℕ) : x (i + k) = x (j + k) := by
    induction k with | zero => rwa [Nat.cast_zero, add_zero, add_zero] | succ k hk => ?_
    rw [Nat.cast_succ, ← add_assoc, ← add_assoc]
    exact h hk
  simpa only [Fin.cast_val_eq_self] using h k

/-- Suppose `p ≠ 0`, and let `(x_i)` be an `(n, p)`-good sequence.
  If `x_{i + j} = x_i`, then `x_{i + jk} = x_i` for any `k`. -/
theorem map_add_nat_mul_of_map_add_nat_eq {j : ℕ} (hx0 : x (i + j) = x i) (k) :
    x (i + (j * k : ℕ)) = x i := by
  induction k with | zero => rw [Nat.mul_zero, Nat.cast_zero, add_zero] | succ k hk => ?_
  rw [Nat.mul_succ, Nat.cast_add, ← add_assoc,
    add_right_comm, hx.map_add_eq_of_map_eq hp hx0, hk]

/-- If `p ≠ 0` and `(x_i)` is an `(n, p)`-good sequence such that
  `x_{i + 1} = x_i` for some `i`, then `(x_i)` is constant. -/
theorem const_of_exists_map_add_one_eq (hx0 : ∃ i, x (i + 1) = x i) : ∃ C, ∀ i, x i = C := by
  rcases hx0 with ⟨i, hi⟩
  refine ⟨x i, λ j ↦ ?_⟩
  replace hi : x (i + (1 * (j - i).val : ℕ)) = x i :=
    hx.map_add_nat_mul_of_map_add_nat_eq hp hi _
  rwa [Nat.one_mul, Fin.cast_val_eq_self, add_sub_cancel] at hi

end


/-- If `p ≠ 0` and `(x_i)` is an `(n, p)`-good sequence of *odd length*
  such that `x_{i + 2} = x_i` for some `i`, then `(x_i)` is constant. -/
theorem const_of_exists_map_add_two_eq
    (hm : Odd m) (hp : p ≠ 0) (hx : good m n p x) (hx0 : ∃ i, x (i + 2) = x i) :
    ∃ C, ∀ i, x i = C := by
  rcases hx0 with ⟨i, hi⟩
  refine hx.const_of_exists_map_add_one_eq hp ⟨i, ?_⟩
  replace hm : 2 ∣ m + 1 := by
    rwa [← even_iff_two_dvd, Nat.even_add_one, Nat.not_even_iff_odd]
  replace hi : x (i + (2 * ((m + 1) / 2) : ℕ)) = x i :=
    hx.map_add_nat_mul_of_map_add_nat_eq hp hi _
  rwa [Nat.mul_div_cancel' hm, Nat.cast_succ, Fin.natCast_self, zero_add] at hi

/-
/-- If `p ≠ 0`, any `(0, p)`-good sequence is constant. -/
theorem const_of_exp_eq_zero_p_ne_zero (hp : p ≠ 0) (hx : good m 0 p x) :
    ∃ C, ∀ i, x i = C := by
  refine ⟨x 0, λ i ↦ ?_⟩
  specialize hx (i - 1) (-1)
  rwa [Int.pow_zero, Int.pow_zero, Int.add_right_inj, sub_add_cancel,
    neg_add_cancel, Int.mul_eq_mul_left_iff hp] at hx
-/


section

variable {n : ℕ} (hn : Odd n)
include hn

/-- If `n` is odd and `(x_i)` is `(n, p)`-good, then `(-x_i)` is `(n, p)`-good. -/
theorem neg_of_exp_odd {x : Fin m → ℤ} (hx : good m n p x) : good m n p (-x) := by
  intro i j
  iterate 2 rw [Pi.neg_apply, Pi.neg_apply, hn.neg_pow, Int.mul_neg, ← Int.neg_add]
  exact neg_inj.mpr (hx i j)

/-- If `n` is odd and `p ≤ 0`, then any `(n, p)`-good sequence is constant. -/
theorem const_of_exp_odd_p_nonpos (hp : p ≤ 0) {x : Fin m → ℤ} (hx : good m n p x) :
    ∃ C, ∀ i, x i = C := by
  ---- If `p = 0` then we are done, so assume `p < 0`.
  obtain rfl | hp0 : p = 0 ∨ p < 0 := hp.eq_or_lt
  · refine ⟨x 0, λ i ↦ hn.pow_inj.mp ?_⟩
    simpa only [Int.zero_mul, Int.add_zero] using hx i 0
  ---- WLOG assume that `x_0 ≤ x_1`.
  wlog hx0 : x 0 ≤ x 1 generalizing x
  · obtain ⟨C, hC⟩ : ∃ C, ∀ i, -x i = C :=
      this (hx.neg_of_exp_odd hn) (Int.neg_le_neg_iff.mpr (Int.le_of_not_le hx0))
    exact ⟨-C, λ i ↦ neg_eq_iff_eq_neg.mp (hC i)⟩
  ---- By induction on `i`, we have `x_i ≤ x_{i + 1}` for all `i`.
  replace hx0 (i : ℕ) : x i ≤ x (i + 1) := by
    induction i with | zero => rwa [Nat.cast_zero, zero_add] | succ i hi => ?_
    rwa [← Int.mul_le_mul_left_of_neg hp0, ← Int.add_le_add_iff_left (x i ^ n),
      Nat.cast_succ, hx i (i + 1), Int.add_le_add_iff_right, hn.pow_le_pow]
  replace hx0 (i) : x i ≤ x (i + 1) := by
    simpa only [Fin.cast_val_eq_self] using hx0 i
  ---- By induction on `j`, we have `x_i ≤ x_{i + j}` for all `i` and `j`.
  replace hx0 (i) (j : ℕ) : x i ≤ x (i + j) := by
    induction j with | zero => rw [Nat.cast_zero, add_zero] | succ j hj => ?_
    rw [Nat.cast_succ, ← add_assoc]
    exact hj.trans (hx0 _)
  ---- Thus we get `x_i = x_j` for all `i` and `j`, and we are done.
  replace hx0 (i j) : x i ≤ x j := by
    simpa only [Fin.cast_val_eq_self, add_sub_cancel] using hx0 i (j - i).val
  exact ⟨x 0, λ i ↦ (hx0 i 0).antisymm (hx0 0 i)⟩

/-- If `n` is odd and `p > 0`, then any `(n, p)`-good sequence is `2`-periodic. -/
theorem two_periodic_of_exp_odd_p_pos (hp : p > 0) {x : Fin m → ℤ} (hx : good m n p x) (i) :
    x (i + 2) = x i := by
  ---- WLOG assume that `x_i ≤ x_{i + 2}`.
  wlog hx0 : x i ≤ x (i + 2) generalizing x
  · have h : -x (i + 2) = -x i :=
      this (hx.neg_of_exp_odd hn) (Int.neg_le_neg_iff.mpr (Int.le_of_not_le hx0))
    exact neg_inj.mp h
  ---- Notice that `x_j ≤ x_k` implies `x_{j + 1} ≥ x_{k + 1}`.
  have h {j k} (hjk : x j ≤ x k) : x (k + 1) ≤ x (j + 1) := by
    rwa [← Int.mul_le_mul_left hp, ← Int.add_le_add_iff_left (x j ^ n),
      hx j k, Int.add_le_add_iff_right, hn.pow_le_pow]
  ---- By induction on `j`, we get `x_{i + 2j} ≤ x_{i + 2(j + 1)}` for all `j`.
  replace h (j : ℕ) : x (i + (2 * j : ℕ)) ≤ x (i + (2 * (j + 1) : ℕ)) := by
    induction j with | zero => rwa [Nat.cast_zero, add_zero, Nat.cast_two] | succ j hj => ?_
    replace hj : x (i + (2 * j : ℕ) + 1 + 1) ≤ x (i + (2 * (j + 1) : ℕ) + 1 + 1) := h (h hj)
    rw [add_assoc _ 1 1, add_assoc _ 1 1, one_add_one_eq_two] at hj
    iterate 2 rw [Nat.mul_succ, Nat.cast_add, ← add_assoc]
    rwa [Nat.cast_two]
  ---- Then we get `x_{i + 2} ≤ x_{i + 2(j + 1)}` for all `j`.
  replace h (j : ℕ) : x (i + 2) ≤ x (i + (2 * (j + 1) : ℕ)) := by
    induction j with | zero => rw [Nat.cast_two] | succ j hj => exact hj.trans (h _)
  ---- Plugging `j = m - 1` gives the desired inequality.
  specialize h (m - 1)
  rw [Nat.sub_add_cancel NeZero.one_le, Nat.two_mul,
    Nat.cast_add, Fin.natCast_self, add_zero, add_zero] at h
  exact h.antisymm hx0

/-- If `n` is odd, then any `(n, p)`-good sequence of odd length is constant. -/
theorem const_of_exp_odd_length_odd (hm : Odd m) {x : Fin m → ℤ} (hx : good m n p x) :
    ∃ C, ∀ i, x i = C := by
  obtain hp | hp : p ≤ 0 ∨ p > 0 := (Int.lt_or_le 0 p).symm
  exacts [const_of_exp_odd_p_nonpos hn hp hx,
    hx.const_of_exists_map_add_two_eq hm hp.ne.symm
      ⟨0, hx.two_periodic_of_exp_odd_p_pos hn hp 0⟩]

end


section

open Finset

/-- A general formula for `(2k, p)`-good sequences. -/
theorem formula_of_exp_two_mul {x : Fin m → ℤ} (hx : good m (2 * k) p x) :
    (∏ i, (x i ^ k + x (i + 1) ^ k)) * ∏ i, (x i ^ k - x (i + 1) ^ k)
      = (-p) ^ m * ∏ i, (x i - x (i + 1)) := calc
  _ = ∏ i, ((x i ^ k + x (i + 1) ^ k) * (x i ^ k - x (i + 1) ^ k)) := prod_mul_distrib.symm
  _ = ∏ i, (-p * (x (i + 1) - x (i + 1 + 1))) := by
    refine prod_congr rfl λ i _ ↦ ?_
    rw [← sq_sub_sq, ← Int.pow_mul, ← Int.pow_mul, Nat.mul_comm, Int.neg_mul, ← Int.mul_neg,
      Int.neg_sub, Int.mul_sub, sub_eq_sub_iff_add_eq_add, hx i (i + 1), Int.add_comm]
  _ = (-p) ^ m * ∏ i, (x (i + 1) - x (i + 1 + 1)) := by
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  _ = (-p) ^ m * ∏ i, (x i - x (i + 1)) :=
    congrArg ((-p) ^ m * ·) (Fintype.prod_equiv (Equiv.addRight 1) _ _ λ _ ↦ rfl)

/-- A general formula for `(2k, p)`-good sequences with adjacent terms being distinct. -/
theorem formula_of_exp_two_mul2
    {x : Fin m → ℤ} (hx : good m (2 * k) p x) (hx0 : ∀ i, x (i + 1) ≠ x i) :
    (∏ i, (x i ^ k + x (i + 1) ^ k)) * ∏ i, (x i ^ k - x (i + 1) ^ k) / (x i - x (i + 1))
      = (-p) ^ m := by
  have h : ∏ i, (x i - x (i + 1)) ≠ 0 :=
    prod_ne_zero_iff.mpr λ i _ ↦ sub_ne_zero_of_ne (hx0 i).symm
  have h0 : (∏ i, (x i ^ k - x (i + 1) ^ k) / (x i - x (i + 1))) * ∏ i, (x i - x (i + 1))
      = ∏ i, (x i ^ k - x (i + 1) ^ k) :=
    prod_mul_distrib.symm.trans <| prod_congr rfl λ i _ ↦
      Int.ediv_mul_cancel (sub_dvd_pow_sub_pow _ _ k)
  rw [← Int.mul_eq_mul_right_iff h, Int.mul_assoc, h0, hx.formula_of_exp_two_mul]

/-- If `(x_i)` is a `(2k, p)`-good sequence with adjacent terms being distinct,
  then `∏_i (x_i^k + x_{i + 1}^k) ∣ p^m`. -/
theorem dvd_of_exp_two_mul
    {x : Fin m → ℤ} (hx : good m (2 * k) p x) (hx0 : ∀ i, x (i + 1) ≠ x i) :
    ∏ i, (x i ^ k + x (i + 1) ^ k) ∣ p ^ m := by
  refine ⟨(-1) ^ m * ∏ i, (x i ^ k - x (i + 1) ^ k) / (x i - x (i + 1)), ?_⟩
  rw [Int.mul_left_comm, hx.formula_of_exp_two_mul2 hx0,
    ← Int.mul_pow, Int.neg_one_mul, Int.neg_neg]

/-- If `p` is odd, then any `(2k, p)`-good sequence of odd length is constant. -/
theorem const_of_exp_two_mul_and_p_odd
    {k p} (hm : Odd m) (hp : Odd p) {x : Fin m → ℤ} (hx : good m (2 * k) p x) :
    ∃ C, ∀ i, x i = C := by
  ---- If `x_{i + 1} = x_i` for some `i` then we are done.
  obtain hx0 | hx0 : (∃ i, x (i + 1) = x i) ∨ (∀ i, x (i + 1) ≠ x i) :=
    Classical.exists_or_forall_not _
  · exact hx.const_of_exists_map_add_one_eq (λ hp0 ↦ Int.not_odd_zero (hp0 ▸ hp)) hx0
  ---- If not, `dvd_of_exp_two_mul` implies `x_i^k + x_{i + 1}^k ≡ 1 (mod 2)` for each `i`.
  replace hx0 : Odd (∏ i, (x i ^ k + x (i + 1) ^ k)) :=
    odd_of_dvd_Int (Int.odd_pow.mpr (Or.inl hp)) (hx.dvd_of_exp_two_mul hx0)
  replace hx0 (i) : (x i ^ k + x (i + 1) ^ k) % 2 = 1 :=
    Int.odd_iff.mp (odd_prod_Int_Fintype.mp hx0 i)
  ---- Summing over all `i` yields a contradiction.
  refine absurd ?_ Int.zero_ne_one
  calc 0
    _ = (∑ i, x i ^ k + ∑ i, x i ^ k) % 2 := by rw [← Int.two_mul, Int.mul_emod_right]
    _ = (∑ i, x i ^ k + ∑ i, x (i + 1) ^ k) % 2 :=
      congrArg (λ n ↦ (_ + n) % 2) (Fintype.sum_equiv (Equiv.addRight 1) _ _ λ _ ↦ rfl).symm
    _ = (∑ i, (x i ^ k + x (i + 1) ^ k) % 2) % 2 := by rw [← sum_add_distrib, sum_int_mod]
    _ = (∑ i : Fin m, 1) % 2 := congrArg (· % 2) (sum_congr rfl λ i _ ↦ hx0 i)
    _ = m % 2 := by rw [sum_const, nsmul_one, card_univ, Fintype.card_fin]
    _ = 1 := by rwa [← Int.odd_iff, Int.odd_coe_nat]

/-- If `(x_i)` is a `(2k, p)`-good sequence, then `(-x_i)` is `(2k, -p)`-good. -/
theorem neg_of_exp_even {x : Fin m → ℤ} (hx : good m (2 * k) p x) :
    good m (2 * k) (-p) (-x) := by
  intro i j; simp_rw [Pi.neg_apply, Int.neg_mul_neg, Int.neg_pow (n := 2 * k)]
  rw [Nat.mul_mod_right, Int.pow_zero, Int.one_mul, Int.one_mul, hx i j]

/-- If `|p| = 2`, then any `(2k, p)`-good sequence of odd length is constant. -/
theorem const_of_exp_two_mul_and_abs_p_eq_two
    {k p} (hm : Odd m) (hp : p.natAbs = 2) {x : Fin m → ℤ} (hx : good m (2 * k) p x) :
    ∃ C, ∀ i, x i = C := by
  ---- To reduce work, WLOG assume `p = 2`.
  wlog hp0 : p = 2 generalizing p x
  · obtain ⟨C, hC⟩ : ∃ C, ∀ i, -x i = C :=
      this (p.natAbs_neg.trans hp) hx.neg_of_exp_even
        ((Int.natAbs_eq_iff.mp hp).elim hp0.elim neg_eq_iff_eq_neg.mpr)
    exact ⟨-C, λ i ↦ neg_eq_iff_eq_neg.mp (hC i)⟩
  subst hp0; replace hp : (2 : ℤ) ≠ 0 := by decide
  ---- If `x_{i + 1} = x_i` for some `i` then again we are done, so assume otherwise.
  obtain hx0 | hx0 : (∃ i, x (i + 1) = x i) ∨ (∀ i, x (i + 1) ≠ x i) :=
    Classical.exists_or_forall_not _
  · exact hx.const_of_exists_map_add_one_eq hp hx0
  ---- Start with `2 ∣ x_i^k + x_j^k` for each `i, j` from the original equation.
  replace h (i j) : 2 ∣ x i ^ k + x j ^ k := by
    have h : x i ^ (2 * k) - x j ^ (2 * k) = 2 * (x (j + 1) - x (i + 1)) := by
      rw [Int.mul_sub, sub_eq_sub_iff_add_eq_add, hx i j, Int.add_comm]
    replace h : 2 ∣ x i ^ (2 * k) - x j ^ (2 * k) := ⟨x (j + 1) - x (i + 1), h⟩
    rw [← even_iff_two_dvd, Int.even_sub, Int.even_pow, Int.even_pow,
      Nat.mul_ne_zero_iff, and_iff_right (Nat.succ_ne_zero 1)] at h
    rwa [← even_iff_two_dvd, Int.even_add, Int.even_pow, Int.even_pow]
  ---- Combining with `dvd_of_exp_two_mul` gives `∏_i, (x_i^k + x_{i + 1}^k)/2 ∣ 1`.
  have h0 : 2 ^ m * ∏ i, (x i ^ k + x (i + 1) ^ k) / 2 ∣ 2 ^ m := calc
    _ = ∏ i, 2 * ((x i ^ k + x (i + 1) ^ k) / 2) := by
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    _ = ∏ i, (x i ^ k + x (i + 1) ^ k) :=
      prod_congr rfl λ i _ ↦ Int.mul_ediv_cancel' (h i (i + 1))
    _ ∣ 2 ^ m := hx.dvd_of_exp_two_mul hx0
  replace h0 : ∏ i, (x i ^ k + x (i + 1) ^ k) / 2 ∣ 1 := by
    rwa [← Int.mul_dvd_mul_iff_left (Int.pow_ne_zero hp (m := m)), Int.mul_one]
  ---- Thus we get `|x_i^k + x_{i + 1}^k| = 2` for each `i`.
  replace h0 : ∀ i, ((x i ^ k + x (i + 1) ^ k) / 2).natAbs = 1 := by
    rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_one, Nat.dvd_one,
      natAbs_prod_Int, prod_eq_one_Nat_Fintype] at h0
  replace h0 (i) : (x i ^ k + x (i + 1) ^ k).natAbs = 2 := by
    rw [← Int.mul_ediv_cancel' (h _ _), Int.natAbs_mul, h0]; rfl
  ---- Then for any `i`, we have `x_{i + 1}^k + x_{i + 2}^k = ±(x_i^k + x_{i + 2}^k)`.
  replace h (i) : x (i + 2) ^ k = x i ^ k
      ∨ x (i + 1) ^ k + x (i + 2) ^ k = -(x i ^ k + x (i + 1) ^ k) := by
    rw [← Int.add_right_inj (x (i + 1) ^ k), ← one_add_one_eq_two, ← add_assoc,
      Int.add_comm _ (x i ^ k), ← Int.natAbs_eq_natAbs_iff, h0, h0]
  ---- If the first case holds for some `i`, then we are done.
  obtain ⟨i, hi⟩ | h1 : (∃ i, x (i + 2) ^ k = x i ^ k) ∨ (∀ i, x (i + 2) ^ k ≠ x i ^ k) :=
    Classical.exists_or_forall_not _
  · refine hx.const_of_exists_map_add_two_eq hm hp ⟨i + 1, ?_⟩
    replace h := hx (i + 2) i
    rwa [Nat.mul_comm 2 k, Int.pow_mul, Int.pow_mul, hi,
      Int.add_right_inj, add_right_comm, Int.mul_eq_mul_left_iff hp] at h
  ---- Otherwise, we get `x_{i + 1}^k + x_{i + 2}^k = -(x_i^k + x_{i + 1}^k)` for all `i`.
  replace h (i) : x (i + 1) ^ k + x (i + 2) ^ k = -(x i ^ k + x (i + 1) ^ k) :=
    (h i).resolve_left (h1 i)
  ---- By induction, `x_i^k + x_{i + 1}^k = (-1)^i (x_0^k + x_1^k)` for all `i`.
  replace h (i : ℕ) : x i ^ k + x (i + 1) ^ k = (-1) ^ i * (x 0 ^ k + x 1 ^ k) := by
    induction i with
    | zero => rw [Nat.cast_zero, zero_add, Int.pow_zero, Int.one_mul]
    | succ i hi => rw [Nat.cast_succ, add_assoc, one_add_one_eq_two,
        h, hi, ← Int.neg_mul, Int.pow_succ, Int.mul_neg_one]
  ---- In particular, we get `x_0^k + x_1^k = (-1)^m (x_0^k + x_1^k) = -(x_0^k + x_1^k)`.
  replace h : x 0 ^ k + x 1 ^ k = -(x 0 ^ k + x 1 ^ k) := calc
    _ = x m ^ k + x (m + 1) ^ k := by rw [Fin.natCast_self, zero_add]
    _ = -(x 0 ^ k + x 1 ^ k) := by rw [h, hm.neg_one_pow, Int.neg_one_mul]
  ---- But then `x_0^k + x_1^k = 0`, contradicting `|x_0^k + x_1^k| = 2`.
  replace h : x 0 ^ k + x 1 ^ k = 0 := self_eq_neg.mp h
  replace h0 : (x 0 ^ k + x (0 + 1) ^ k).natAbs = 2 := h0 0
  rw [zero_add, h, Int.natAbs_zero] at h0
  exact absurd h0.symm (Nat.succ_ne_zero 1)

end

end good


/-- Final solution -/
theorem final_solution {m n p} [NeZero m] (hm : Odd m) (hp : Odd p ∨ p.natAbs = 2)
    {x : Fin m → ℤ} (hx : good m n p x) : ∃ C, ∀ i, x i = C := by
  obtain hn | ⟨k, rfl⟩ : Odd n ∨ 2 ∣ n :=
    (Nat.even_or_odd n).symm.imp_right even_iff_two_dvd.mp
  exacts [hx.const_of_exp_odd_length_odd hn hm,
    hp.elim (hx.const_of_exp_two_mul_and_p_odd hm)
      (hx.const_of_exp_two_mul_and_abs_p_eq_two hm)]
