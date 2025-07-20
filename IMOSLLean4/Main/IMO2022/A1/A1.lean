/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Basic

/-!
# IMO 2022 A1

Let $R$ be a totally ordered ring.
Let $(a_n)_{n ≥ 0}$ be a sequence of non-negative elements of $R$ such that for any $n ∈ ℕ$,
$$ a_{n + 1}^2 + a_n a_{n + 2} ≤ a_n + a_{n + 2}. $$
Show that $a_N ≤ 1$ for all $N ≥ 2$.
-/

namespace IMOSL
namespace IMO2022A1

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

lemma main_ineq {a b c : R} (h : 1 ≤ a) (h0 : 1 < b)
    (h1 : 0 ≤ c) (h2 : b ^ 2 + a * c ≤ a + c) : b < a :=
  lt_of_add_lt_add_right <| h2.trans_lt' <|
    add_lt_add_of_lt_of_le (lt_self_pow₀ h0 (Nat.lt_succ_self 1))
      (le_mul_of_one_le_left h1 h)

lemma main_ineq2 {a b c : R} (h : 0 ≤ a) (h0 : 1 < b)
    (h1 : 1 ≤ c) (h2 : b ^ 2 + a * c ≤ a + c) : b < c :=
  lt_of_add_lt_add_left <| h2.trans_lt' <| (add_comm a b).trans_lt <|
    add_lt_add_of_lt_of_le (lt_self_pow₀ h0 (Nat.lt_succ_self 1))
      (le_mul_of_one_le_right h h1)



/-- Final solution -/
theorem final_solution {a : ℕ → R} (h : ∀ i, 0 ≤ a i)
    (h0 : ∀ i, a (i + 1) ^ 2 + a i * a (i + 2) ≤ a i + a (i + 2))
    (N : ℕ) (h1 : 2 ≤ N) : a N ≤ 1 := by
  -- First get that `a_{i + 1} > 1 → ¬a_{i + 2} > 1`
  have h2 (i : ℕ) (h1 : 1 < a (i + 1)) (h2 : 1 < a (i + 2)) : False :=
    (main_ineq h1.le h2 (h _) (h0 _)).asymm (main_ineq2 (h i) h1 h2.le (h0 _))
  -- Now use the above to finish
  rcases Nat.exists_eq_add_of_le' h1 with ⟨n, rfl⟩
  refine le_of_not_gt λ h1 ↦ (h0 (n + 1)).not_gt ?_
  rw [← sub_lt_iff_lt_add, add_sub_assoc, ← one_sub_mul]
  exact (one_lt_pow₀ h1 (Nat.succ_ne_zero 1)).trans_le' <|
    add_le_of_le_sub_left <| mul_le_of_le_one_right
      (sub_nonneg_of_le <| le_of_not_gt λ h3 ↦ h2 _ h3 h1)
      (le_of_not_gt (h2 _ h1))
