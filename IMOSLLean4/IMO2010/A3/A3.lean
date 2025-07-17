/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Bounds.Defs

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

def good [AddCommMonoid M] [LinearOrder M] (c : M) (x : ℕ → M) :=
  ∀ i, x i + x (i + 1) + x (i + 2) ≤ 2 • c

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

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
    mul_comm z, ← sq, add_comm, two_nsmul, ← two_mul] at h1
  exact le_of_add_le_add_right (h1.trans (two_mul_le_add_sq _ _))

theorem good_targetSum_le {x : ℕ → R} (h : ∀ i, 0 ≤ x i) {c : R} (h0 : good c x) :
    ∀ n, targetSum x (2 * n) ≤ n • c ^ 2
  | 0 => by rw [targetSum, sum_range_zero, zero_nsmul]
  | n + 1 => by
      rw [targetSum, Nat.mul_succ, sum_range_succ, sum_range_succ, add_assoc, succ_nsmul]
      exact add_le_add (good_targetSum_le h h0 n) (special_ineq (h _) (h _) (h0 _) (h0 _))

open Fin.NatCast in
omit [ExistsAddOfLE R] in
theorem targetSum_of_Fin2Map (c : R) :
    ∀ n, targetSum (λ n ↦ ![c, 0] n) (2 * n) = n • c ^ 2
  | 0 => by rw [Nat.mul_zero, targetSum, sum_range_zero, zero_nsmul]
  | n + 1 => by
      have h (n) : ((2 * n : ℕ) : Fin 2) = 0 := Fin.val_injective (Nat.mul_mod_right 2 n)
      have h0 (n) : ((2 * n + 1 : ℕ) : Fin 2) = 1 := Fin.val_injective (Nat.mul_add_mod 2 n 1)
      rw [Nat.mul_succ, targetSum, sum_range_succ, sum_range_succ,
        ← targetSum, targetSum_of_Fin2Map, succ_nsmul, add_assoc,
        add_right_inj, h, add_right_comm, ← Nat.mul_succ, h, h0, h0]
      change c * c + 0 * 0 = c ^ 2; rw [sq, mul_zero, add_zero]





/-! ### Summary -/

structure goodPeriodicSeq (c n) where
  x : ℕ → R
  nonneg : ∀ i, 0 ≤ x i
  good : good c x
  periodic : ∀ k, x (k + 2 * n) = x k

open Fin.NatCast in
def Fin2Map_goodPeriodicSeq {c : R} (h : 0 ≤ c) (n) : goodPeriodicSeq c n :=
  { x := λ n ↦ ![c, 0] n
    nonneg := λ i ↦ Fin.cases h (λ i ↦ Fin.fin_one_eq_zero i ▸ le_refl 0) i
    good := λ i ↦ by
      have h0 : ((i + 1 : ℕ) : Fin 2) = i + 1 := Fin.val_injective (i.mod_add_mod 2 1).symm
      have h1 : ((i + 2 : ℕ) : Fin 2) = i := Fin.val_injective (i.add_mod_right 2)
      simp only; rw [h0, h1, two_nsmul]; clear h0 h1
      refine Fin.cases (congrArg₂ _ (add_zero c) rfl).le (λ i ↦ ?_) i
      rw [Fin.fin_one_eq_zero i]; change 0 + c + 0 ≤ c + c
      rw [zero_add, add_zero]; exact le_add_of_nonneg_left h
    periodic := λ i ↦  congrArg _ (Fin.val_injective (Nat.add_mul_mod_self_left i 2 n)) }

/-- Final solution -/
theorem final_solution {c : R} (h : 0 ≤ c) (n : ℕ) :
    IsGreatest (Set.range λ (X : goodPeriodicSeq c n) ↦ targetSum X.x (2 * n)) (n • c ^ 2) :=
  ⟨⟨Fin2Map_goodPeriodicSeq h n, targetSum_of_Fin2Map c n⟩,
  λ _ ⟨X, h0⟩ ↦ h0.symm.trans_le (good_targetSum_le X.nonneg X.good n)⟩
