/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring

/-!
# IMO 2021 A7

Let $R$ be a totally ordered commutative ring.
Let $(x_n)_{n ≥ 0}$ be a sequence of elements of $R$ such that, for each $n ∈ ℕ$,
$$ x_{n + 1} x_{n + 2} ≥ x_n^2 + 1. $$
Show that for any $N ∈ ℕ$,
$$ 27 (x_0 + x_1 + … + x_{N + 1})^2 > 8 N^3. $$
-/

namespace IMOSL
namespace IMO2021A7

open Finset

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

lemma lemma1 (a b c : R) :
    (b + 2 * c) ^ 2 + 6 * (a * b) ≤ (a + 2 * b) ^ 2 + 6 * c ^ 2 := by
  obtain ⟨x, hx⟩ : ∃ x, (a + 2 * b) ^ 2 = x ^ 2 + 3 * b ^ 2 + 6 * (a * b) := by
    obtain ⟨d, rfl⟩ | ⟨d, rfl⟩ : (∃ d, b = a + d) ∨ (∃ d, a = b + d) :=
      (le_total a b).imp exists_add_of_le exists_add_of_le
    all_goals exact ⟨d, by ring⟩
  obtain ⟨y, hy⟩ : ∃ y, 3 * b ^ 2 + 6 * c ^ 2 = 2 * y ^ 2 + (b + 2 * c) ^ 2 := by
    obtain ⟨d, rfl⟩ | ⟨d, rfl⟩ : (∃ d, c = b + d) ∨ (∃ d, b = c + d) :=
      (le_total b c).imp exists_add_of_le exists_add_of_le
    all_goals exact ⟨d, by ring⟩
  rw [hx, add_right_comm, add_le_add_iff_right,
    add_assoc, hy, ← add_assoc, le_add_iff_nonneg_left]
  exact add_nonneg (sq_nonneg x) (mul_nonneg zero_le_two (sq_nonneg y))

lemma lemma1_strict {a b c : R} (h : c ^ 2 + 1 ≤ a * b) :
    (b + 2 * c) ^ 2 + 6 ≤ (a + 2 * b) ^ 2 := by
  refine le_of_add_le_add_right (a := 6 * c ^ 2) ((lemma1 _ _ _).trans' ?_)
  rw [add_assoc, add_le_add_iff_left, add_comm, ← mul_add_one 6 (c ^ 2)]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

lemma lemma2 (r : R) {y : ℕ → R} (hy : ∀ n, 0 ≤ y n) (hy0 : ∀ n, n • r ≤ y n ^ 2) (N) :
    (4 * N ^ 3) • r ≤ (3 * (range (N + 1)).sum y) ^ 2 := by
  ---- Discharge the case `r ≤ 0`
  obtain hr | hr : r ≤ 0 ∨ 0 ≤ r := le_total r 0
  · exact (nsmul_nonpos hr _).trans (sq_nonneg _)
  ---- Induction on `N`; base case `N = 0` immediate
  induction' N with N N_ih
  · rw [Nat.zero_pow (Nat.succ_pos 2), mul_zero, zero_nsmul]
    exact sq_nonneg _
  ---- Now focus on the induction step with `r ≥ 0`
  replace hy0 : (9 * (N + 1)) • r ≤ (3 * y (N + 1)) ^ 2 := by
    have h : 9 = 3 ^ 2 := rfl
    rw [mul_nsmul', nsmul_eq_mul, h, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
    exact mul_le_mul_of_nonneg_left (hy0 (N + 1)) (sq_nonneg 3)
  ---- Partial calculation
  suffices ((4 * N + 1) * (3 * N)) • r ≤ 2 * (3 * (range (N + 1)).sum y) * (3 * y (N + 1))
  by calc
    _ ≤ (4 * (N + 1) ^ 3 + 5) • r := nsmul_le_nsmul_left hr (Nat.le_add_right _ 5)
    _ = (4 * N ^ 3 + 9 * (N + 1) + (4 * N + 1) * (3 * N)) • r := congrArg₂ _ (by ring) rfl
    _ = (4 * N ^ 3) • r + (9 * (N + 1)) • r + ((4 * N + 1) * (3 * N)) • r := by
      rw [add_nsmul, add_nsmul]
    _ ≤ (3 * (range (N + 1)).sum y) ^ 2 + (3 * y (N + 1)) ^ 2
        + 2 * (3 * (range (N + 1)).sum y) * (3 * y (N + 1)) :=
      add_le_add_three N_ih hy0 this
    _ = (3 * (range (N + 1 + 1)).sum y) ^ 2 := by
      rw [← add_sq', ← mul_add, sum_range_succ _ (N + 1)]
  ---- Prove the estimate `(12N^2 + 3N) r ≤ 18 y_{N + 1} ∑_{i ≤ N} y_N`
  have h : ((4 * N + 1) * (3 * N)) ^ 2 ≤ 2 ^ 2 * (4 * N ^ 3) * (9 * (N + 1)) := by
    obtain rfl | h : N = 0 ∨ 0 < N := N.eq_zero_or_pos
    · exact Nat.le_refl 0
    replace h : (4 * N + 1) ^ 2 ≤ 16 * N * (N + 1) := by
      rw [add_sq, one_pow, mul_one, ← mul_assoc, mul_pow, (16 * N).mul_succ,
        mul_assoc 16, ← sq, Nat.add_mul 8 8 N, ← add_assoc]
      exact Nat.add_le_add_left (Nat.mul_pos (Nat.succ_pos 7) h) _
    rw [mul_pow, ← Nat.mul_assoc (2 ^ 2), N.pow_succ', ← Nat.mul_assoc (2 ^ 2 * 4),
      Nat.mul_comm 9, Nat.mul_mul_mul_comm, (N ^ 2).mul_comm, ← Nat.mul_pow 3 N 2]
    exact Nat.mul_le_mul_right _ h
  have h0 : 0 ≤ 2 * (3 * (range (N + 1)).sum y) * (3 * y (N + 1)) := by
    have X : 0 ≤ (3 : R) := zero_le_three
    refine mul_nonneg ?_ (mul_nonneg X (hy _))
    exact mul_nonneg zero_le_two (mul_nonneg X (sum_nonneg λ n _ ↦ hy n))
  apply le_of_pow_le_pow_left₀ (Nat.succ_ne_zero 1) h0
  calc
    _ = (((4 * N + 1) * (3 * N)) ^ 2 : ℕ) * r ^ 2 := by
      rw [nsmul_eq_mul, mul_pow, ← Nat.cast_pow]
    _ ≤ (2 ^ 2 * (4 * N ^ 3) * (9 * (N + 1)) : ℕ) * r ^ 2 :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) (sq_nonneg r)
    _ = 2 ^ 2 * (((4 * N ^ 3) • r) * ((9 * (N + 1)) • r)) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_two, mul_assoc (2 ^ 2),
        sq r, mul_assoc, mul_mul_mul_comm, nsmul_eq_mul, nsmul_eq_mul]
    _ ≤ 2 ^ 2 * ((3 * (range (N + 1)).sum y) ^ 2 * (3 * y (N + 1)) ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg 2)
      exact mul_le_mul N_ih hy0 (nsmul_nonneg hr _) (sq_nonneg _)
    _ = _ := by rw [← mul_pow, ← mul_pow, ← mul_assoc]

lemma lemma3 [AddCommMonoid M] (x : ℕ → M) (N) :
    (range N).sum (λ i ↦ x (i + 1) + 2 • x i) + (x 0 + 2 • x N)
      = 3 • (range (N + 1)).sum x := by
  rw [sum_add_distrib, add_add_add_comm, ← sum_range_succ,
    ← sum_range_succ', sum_nsmul, ← succ_nsmul']



/-- Final solution -/
theorem final_solution {x : ℕ → R} (hx : ∀ n, 0 ≤ x n)
    (hx0 : ∀ n, x n ^ 2 + 1 ≤ x (n + 1) * x (n + 2)) (N) :
    8 * N ^ 3 < 27 * (range (N + 2)).sum x ^ 2 := by
  let y (n : ℕ) : R := x (n + 1) + 2 * x n
  have h (n) : 0 < x (n + 1) := by
    refine (hx n.succ).lt_or_eq.resolve_right λ h ↦ (hx0 n).not_gt ?_
    rw [← h, zero_mul]; exact add_pos_of_nonneg_of_pos (sq_nonneg _) one_pos
  replace hx0 (n) : y n ^ 2 + 6 ≤ y (n + 1) ^ 2 :=
    lemma1_strict ((hx0 n).trans_eq (mul_comm _ _))
  replace hx0 : ∀ n, n • 6 ≤ y n ^ 2 := by
    refine Nat.rec ((zero_nsmul 6).trans_le (sq_nonneg _)) λ n hn ↦ (hx0 n).trans' ?_
    rwa [succ_nsmul, add_le_add_iff_right]
  have h0 : 0 < (3 : R) := three_pos
  have h1 (n) : 0 ≤ y n := add_nonneg (hx _) (mul_nonneg zero_le_two (hx _))
  calc
    _ ≤ 3 * (range (N + 1)).sum y ^ 2 := by
      refine le_of_mul_le_mul_of_pos_left ?_ h0
      have X : (3 : R) * 8 = (4 * 6 : ℕ) := by
        rw [← Nat.cast_ofNat, ← Nat.cast_ofNat (n := 8), ← Nat.cast_mul]
      rw [← mul_assoc, ← mul_assoc, ← sq, ← mul_pow, X, ← Nat.cast_pow, ← Nat.cast_mul,
        Nat.mul_right_comm, Nat.cast_mul, Nat.cast_ofNat, ← nsmul_eq_mul]
      exact lemma2 6 h1 hx0 N
    _ < 3 * (3 * (range (N + 2)).sum x) ^ 2 := by
      refine mul_lt_mul_of_pos_left ?_ three_pos
      refine pow_lt_pow_left₀ ?_ (sum_nonneg λ n _ ↦ h1 n) (Nat.succ_ne_zero 1)
      rw [← Nat.cast_ofNat (n := 3), ← nsmul_eq_mul, ← lemma3]
      simp only [nsmul_eq_mul]; rw [Nat.cast_two, lt_add_iff_pos_right]
      exact add_pos_of_nonneg_of_pos (hx 0) (mul_pos two_pos (h N))
    _ = 27 * (range (N + 2)).sum x ^ 2 := by rw [mul_pow, ← mul_assoc]; norm_num
