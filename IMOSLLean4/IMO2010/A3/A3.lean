/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Periodic

/-!
# IMO 2010 A3

Fix a positive integer $N$, a totally ordered commutative ring $R$, and an element $c ≥ 0$.
Consider all $2N$-periodic sequences $(x_n)_{n ≥ 0}$ such that for any $n$,
$$ x_n + x_{n + 1} + x_{n + 2} ≤ 2c. $$
Determine the maximum possible value of
$$ \sum_{k = 1}^{2N} (x_k x_{k + 2} + x_{k + 1} x_{k + 3}). $$
-/

namespace IMOSL
namespace IMO2010A3

open Finset

def good [OrderedAddCommMonoid M] (c : M) (x : ℕ → M) :=
  ∀ i, x i + x (i + 1) + x (i + 2) ≤ 2 • c

variable [LinearOrderedCommSemiring R] [ExistsAddOfLE R]

def targetSum (x : ℕ → R) (n : ℕ) := (range n).sum λ i ↦ x i * x (i + 2)

theorem special_ineq {w x y z c : R} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : w + x + y ≤ 2 • c) (h0 : x + y + z ≤ 2 • c) :
    w * y + x * z ≤ c ^ 2 := by
  replace h : w * y + (x + y) * y ≤ (2 • c) * y := by
    rw [← add_mul, ← add_assoc]
    exact mul_le_mul_of_nonneg_right h hy
  replace h0 : (x + y) * x + z * x ≤ (2 • c) * x :=
     add_mul _ _ x ▸ mul_le_mul_of_nonneg_right h0 hx
  have h1 := add_le_add h h0
  rw [add_comm (w * y), add_add_add_comm, ← mul_add, ← mul_add, add_comm y,
    mul_comm z, ← sq, add_comm, nsmul_eq_mul, Nat.cast_two] at h1
  exact le_of_add_le_add_right (h1.trans (two_mul_le_add_sq _ _))

theorem good_targetSum_le {x : ℕ → R} (h : ∀ i, 0 ≤ x i) {c : R} (h0 : good c x) :
    ∀ n, targetSum x (2 * n) ≤ n • c ^ 2
  | 0 => by rw [targetSum, sum_range_zero, zero_nsmul]
  | n + 1 => by
      rw [targetSum, Nat.mul_succ, sum_range_succ, sum_range_succ, add_assoc, succ_nsmul]
      exact add_le_add (good_targetSum_le h h0 n) (special_ineq (h _) (h _) (h0 _) (h0 _))

theorem targetSum_of_Fin2Map (c : R) : ∀ n, targetSum (λ n ↦ ![c, 0] n) (2 * n) = n • c ^ 2
  | 0 => by rw [mul_zero, targetSum, sum_range_zero, zero_nsmul]
  | n + 1 => by
      have h : ((2 : ℕ) : Fin 2) = 0 := rfl
      rw [Nat.mul_succ, targetSum, sum_range_succ, sum_range_succ, ← targetSum,
        targetSum_of_Fin2Map, succ_nsmul, add_assoc, add_right_inj, Nat.cast_add,
        Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_mul, h, zero_mul, sq]
      exact add_right_eq_self.mpr (zero_mul 0)





/-! ### Summary -/

structure goodPeriodicSeq (c n) where
  x : ℕ → R
  nonneg : ∀ i, 0 ≤ x i
  good : good c x
  periodic : x.Periodic (2 * n)

def Fin2Map_goodPeriodicSeq {c : R} (h : 0 ≤ c) (n) : goodPeriodicSeq c n :=
  { x := λ n ↦ ![c, 0] n
    nonneg := λ i ↦ by
      simp only; exact Fin.cases h (λ i ↦ Fin.fin_one_eq_zero i ▸ le_refl 0) i
    good := λ i ↦ by
      simp only; rw [two_nsmul, Nat.cast_succ, Nat.cast_add]
      refine Fin.cases (congrArg₂ _ (add_zero c) rfl).le (λ i ↦ ?_) i
      rw [Fin.fin_one_eq_zero i]; change 0 + c + 0 ≤ c + c
      rw [zero_add, add_zero]; exact le_add_of_nonneg_left h
    periodic := λ i ↦ by
      have h : ((2 : ℕ) : Fin 2) = 0 := rfl
      simp only; rw [Nat.cast_add, Nat.cast_mul, h, zero_mul, add_zero] }

/-- Final solution -/
theorem final_solution {c : R} (h : 0 ≤ c) (n : ℕ) :
    IsGreatest (Set.range λ (X : goodPeriodicSeq c n) ↦ targetSum X.x (2 * n)) (n • c ^ 2) :=
  ⟨⟨Fin2Map_goodPeriodicSeq h n, targetSum_of_Fin2Map c n⟩,
  λ _ ⟨X, h0⟩ ↦ h0.symm.trans_le (good_targetSum_le X.nonneg X.good n)⟩
