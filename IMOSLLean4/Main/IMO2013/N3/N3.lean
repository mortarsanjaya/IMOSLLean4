/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Factors
import Mathlib.Order.MinMax
import Mathlib.Order.Nat

/-!
# IMO 2013 N3

For each positive integer $n$, let $P(n)$ denote the largest prime divisor of $n$.
Prove that there exists infinitely many $n ∈ ℕ$ such that
$$ P(n^4 + n^2 + 1) = P((n + 1)^4 + (n + 1)^2 + 1). $$
-/

namespace IMOSL
namespace IMO2013N3

/-- General result for the main theorem -/
theorem general_result [LinearOrder α]
    {f : ℕ → α} (hf : ∀ n, f ((n + 1) ^ 2) = max (f n) (f (n + 1))) (C) :
    ∃ n, C ≤ n ∧ f (n ^ 2) = f ((n + 1) ^ 2) := by
  by_contra h
  replace h (n) (h0 : C ≤ n) (h1 : f n ≤ f (n + 1)) : f (n + 1) < f (n + 2) := by
    refine not_le.mp λ h2 ↦ h ⟨n + 1, Nat.le_succ_of_le h0, ?_⟩
    rw [hf, hf, max_eq_right h1, max_eq_left h2]
  replace h (n) (h0 : C ≤ n) (h1 : f n ≤ f (n + 1)) : ∀ k, n < k → f k < f (k + 1) :=
    Nat.le_induction (h n h0 h1) (λ k h2 h3 ↦ h k ((Nat.le_succ_of_le h0).trans h2) h3.le)
  replace h (n) (h0 : C ≤ n) (h1 : f n ≤ f (n + 1)) (k) (h2 : n < k) :
      ∀ m, k < m → f k < f m :=
    Nat.le_induction (h n h0 h1 k h2) (λ m h3 ↦ (h n h0 h1 m (h2.trans h3)).trans')
  replace h (n) (h0 : C ≤ n) : f (n + 1) < f n := by
    refine not_le.mp λ h1 ↦ (hf (n + 1)).not_gt ?_
    rw [max_eq_right (h n h0 h1 (n + 1) n.lt_succ_self (n + 2) (n + 1).lt_succ_self).le]
    refine h n h0 h1 (n + 2) (Nat.lt_add_of_pos_right Nat.two_pos) ((n + 2) ^ 2) ?_
    rw [sq, Nat.succ_mul, Nat.lt_add_left_iff_pos]
    exact Nat.mul_pos n.succ_pos n.succ.succ_pos
  have h0 (n) (h0 : C ≤ n) : ∀ k, n ≤ k → f k ≤ f n :=
    Nat.le_induction (le_refl _) (λ k h1 ↦ (h k (h0.trans h1)).le.trans)
  ---- Finishing
  specialize h0 _ C.le_succ ((C + 1) ^ 2) (Nat.le_self_pow (Nat.succ_ne_zero 1) _)
  rw [hf, max_le_iff] at h0
  exact h0.1.not_gt (h C C.le_refl)





/-! ### The original problem -/

theorem foldr_max_append [LinearOrder α] [OrderBot α] :
    ∀ l l' : List α, (l ++ l').foldr max ⊥ = max (l.foldr max ⊥) (l'.foldr max ⊥)
  | [], l' => (max_bot_left _).symm
  | a :: l, l' => by rw [List.cons_append, List.foldr_cons,
      List.foldr_cons, foldr_max_append, max_assoc]

theorem special_formula (n : ℕ) :
    ((n + 1) ^ 2) ^ 2 + (n + 1) ^ 2 + 1 = (n ^ 2 + n + 1) * ((n + 1) ^ 2 + (n + 1) + 1) := by
  rw [sq n, ← Nat.succ_mul, sq n.succ, ← Nat.mul_succ, Nat.succ_mul (n.succ * n),
    Nat.mul_succ (n.succ * _), ← add_assoc, Nat.succ_inj, mul_mul_mul_comm,
    n.succ.mul_succ n.succ, add_add_add_comm, ← n.succ.mul_succ, add_left_inj,
    ← Nat.mul_succ, sq, n.mul_succ, ← Nat.add_succ, ← n.succ_mul]

/-- Final solution -/
theorem final_solution :
    ∀ C, ∃ n ≥ C, (n ^ 4 + n ^ 2 + 1).primeFactorsList.foldr max ⊥
      = ((n + 1) ^ 4 + (n + 1) ^ 2 + 1).primeFactorsList.foldr max ⊥ := by
  simp only [Nat.pow_mul _ 2 2]
  refine general_result (f := λ n ↦ (n ^ 2 + n + 1).primeFactorsList.foldr max ⊥) λ n ↦ ?_
  simp only; rw [special_formula, ← foldr_max_append]
  have h0 (n) : n ^ 2 + n + 1 ≠ 0 := Nat.succ_ne_zero _
  exact (Nat.perm_primeFactorsList_mul (h0 n) (h0 (n + 1))).foldr_eq _
