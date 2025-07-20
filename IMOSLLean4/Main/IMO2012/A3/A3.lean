/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# IMO 2012 A3 (P2)

Let $R$ be a totally ordered commutative ring and $x_0, x_1, …, x_n ∈ R$
  (with $n ≥ 1$) be positive elements such that $x_0 x_1 … x_n = 1$.
Prove that $$ (1 + x_0)^2 (1 + x_1)^3 … (1 + x_n)^{n + 2} > (n + 2)^{n + 2}. $$
-/

namespace IMOSL
namespace IMO2012A3

section

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

theorem bernoulli_side_ineq (x y : R) (n : ℕ) :
    y * (n.succ * x + y) ≤ (n * x + y) * (x + y) := calc
  _ ≤ y * (n.succ * x + y) + n • x ^ 2 :=
    le_add_of_nonneg_right (nsmul_nonneg (sq_nonneg x) n)
  _ = y * (n * x + x + y) + n * x ^ 2 := by rw [Nat.cast_succ, add_one_mul, nsmul_eq_mul]
  _ = _ := by ring

lemma bernoulli_ineq_aux (x) {y : R} (hy : 0 ≤ y) (n) :
    y ^ n.succ * (n.succ.succ * x + y) ≤ y ^ n * (n.succ * x + y) * (x + y) := by
  rw [pow_succ, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (bernoulli_side_ineq x y _) (pow_nonneg hy n)

theorem bernoulli_ineq {x y : R} (hy : 0 ≤ y) (h : 0 ≤ x + y) :
    ∀ n, y ^ n * (n.succ * x + y) ≤ (x + y) ^ n.succ := by
  refine Nat.rec ?_ λ n hn ↦ ?_
  · rw [pow_zero, one_mul, Nat.cast_one, one_mul, pow_one]
  · rw [pow_succ' (x + y), add_mul, Nat.cast_succ, add_one_mul,
      add_comm _ x, add_assoc, mul_add, mul_comm]
    refine add_le_add ?_ ?_
    · obtain hx | hx : 0 ≤ x ∨ x ≤ 0 := le_total 0 x
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy (le_add_of_nonneg_left hx) _) hx
      · exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ h (add_le_of_nonpos_left hx) _) hx
    · rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left hn hy

theorem bernoulli_ineq_strict {x y : R} (hy : 0 ≤ y) (h : 0 < x + y) (hx : x ≠ 0) :
    ∀ n : ℕ, y ^ n.succ * (n.succ.succ * x + y) < (x + y) ^ n.succ.succ := by
  refine Nat.rec ?_ λ n hn ↦ ?_
  · rw [pow_one, mul_comm, add_mul, ← sq, add_sq, add_assoc]
    exact lt_add_of_pos_left _ (sq_pos_iff.mpr hx)
  · apply (bernoulli_ineq_aux _ hy _).trans_lt
    rw [pow_succ (x + y)]; exact mul_lt_mul_of_pos_right hn h

end


variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem bernoulli_special1 {x : R} (hy : -1 ≤ x) (n : ℕ) :
    (n + 2 : ℕ) ^ (n + 2) * x ≤ (n + 1 : ℕ) ^ (n + 1) * (1 + x) ^ (n + 2) := by
  have h : n.succ * x - 1 + (n + 2 : ℕ) = n.succ * (x + 1) := by
    rw [(n + 1).cast_succ, sub_add_add_cancel, mul_add_one]
  have h0 : 0 ≤ n.succ * x - 1 + (n + 2 : ℕ) :=
    (mul_nonneg n.succ.cast_nonneg (neg_le_iff_add_nonneg.mp hy)).trans_eq h.symm
  replace h0 := bernoulli_ineq (n + 2).cast_nonneg h0 (n + 1)
  rw [(n + 1).cast_succ, add_one_mul, add_assoc, ← Nat.cast_succ, h, ← mul_add,
    mul_pow, pow_succ (n.succ : R), sub_add_add_cancel, ← add_one_mul,
    ← Nat.cast_succ, ← mul_assoc, ← mul_assoc, mul_right_comm _ (n.succ : R),
    ← pow_succ, mul_right_comm, mul_right_comm _ (n.succ : R), add_comm x] at h0
  exact le_of_mul_le_mul_of_pos_right h0 (Nat.cast_pos.mpr n.succ_pos)

theorem bernoulli_special2 {x : R} (hx : -1 < x) {n : ℕ} (hx0 : n.succ * x ≠ 1) :
    (n + 2 : ℕ) ^ (n + 2) * x < (n + 1 : ℕ) ^ (n + 1) * (1 + x) ^ (n + 2) := by
  have h : n.succ * x - 1 + (n + 2 : ℕ) = n.succ * (x + 1) := by
    rw [(n + 1).cast_succ, sub_add_add_cancel, mul_add_one]
  have h0 : 0 < n.succ * x - 1 + (n + 2 : ℕ) :=
    (mul_pos (Nat.cast_pos.mpr n.succ_pos) (neg_lt_iff_pos_add.mp hx)).trans_eq h.symm
  replace h0 := bernoulli_ineq_strict (n + 2).cast_nonneg h0 (sub_ne_zero.mpr hx0) n
  rw [(n + 1).cast_succ, add_one_mul, add_assoc, ← Nat.cast_succ, h, ← mul_add,
    mul_pow, pow_succ (n.succ : R), sub_add_add_cancel, ← add_one_mul,
    ← Nat.cast_succ, ← mul_assoc, ← mul_assoc, mul_right_comm _ (n.succ : R),
    ← pow_succ, mul_right_comm, mul_right_comm _ (n.succ : R), add_comm x] at h0
  exact lt_of_mul_lt_mul_of_nonneg_right h0 n.succ.cast_nonneg


open Finset

variable {x : ℕ → R} (hx : ∀ n, 0 < x n)
include hx

theorem main_ineq {n : ℕ} (hn : ∃ k ∈ range n, (k + 1 : ℕ) * x k ≠ 1) :
    (n + 1 : ℕ) ^ (n + 1) * ∏ i ∈ range n, x i < ∏ i ∈ range n, (1 + x i) ^ (i + 2) := by
  rcases hn with ⟨k, hkn, hk⟩
  have h : ∏ i ∈ range n, (i + 2 : ℕ) ^ (i + 2) * x i
      < ∏ i ∈ range n, (i + 1 : ℕ) ^ (i + 1) * (1 + x i) ^ (i + 2) :=
    prod_lt_prod
      (λ i _ ↦ mul_pos (pow_pos (Nat.cast_pos.mpr (i + 1).succ_pos) _) (hx i))
      (λ i _ ↦ bernoulli_special1 (neg_one_lt_zero.trans (hx i)).le _)
      ⟨k, hkn, bernoulli_special2 (neg_one_lt_zero.trans (hx k)) hk⟩
  have h0 : ∏ i ∈ range n, ((i + 2 : ℕ) : R) ^ (i + 2)
      = (n + 1 : ℕ) ^ (n + 1) * ∏ i ∈ range n, ((i + 1 : ℕ) : R) ^ (i + 1) := by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt (mem_range.mp hkn))
    rw [prod_range_succ, prod_range_succ', Nat.cast_one, one_pow, mul_one, mul_comm]
  rw [prod_mul_distrib, prod_mul_distrib, h0, mul_right_comm, mul_comm] at h
  apply lt_of_mul_lt_mul_of_nonneg_left h
  exact prod_nonneg λ i _ ↦ pow_nonneg (i + 1).cast_nonneg _

/-- Final solution -/
theorem final_solution (hn : 1 < n) (hn0 : ∏ k ∈ range n, x k = 1) :
    (n + 1 : ℕ) ^ (n + 1) < ∏ i ∈ range n, (1 + x i) ^ (i + 2) := by
  calc
    _ = (n + 1 : ℕ) ^ (n + 1) * ∏ i ∈ range n, x i := by rw [hn0, mul_one]
    _ < ∏ i ∈ range n, (1 + x i) ^ (i + 2) := main_ineq hx ?_
  by_contra hn1; simp only [not_exists, not_and, not_not] at hn1
  replace hn1 : ∏ k ∈ range n, (k + 1 : ℕ) * x k = 1 := prod_eq_one hn1
  rw [prod_mul_distrib, hn0, mul_one, ← Nat.cast_prod, Nat.cast_eq_one] at hn1
  replace hn0 : 2 ∣ ∏ i ∈ range n, (i + 1) := dvd_prod_of_mem _ (mem_range.mpr hn)
  rw [hn1, Nat.dvd_one] at hn0
  revert hn0; exact Nat.succ_ne_self 1
