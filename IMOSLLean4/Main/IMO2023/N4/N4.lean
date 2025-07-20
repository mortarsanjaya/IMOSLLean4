/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# IMO 2023 N4

Let $a_0, a_1, …, a_{n - 1}, b_0, b_1, …, b_{n - 1} ∈ ℕ^+$ and
  $D$ be a positive integer such that for each $i ≤ n$,
$$ b_0 b_1 … b_i a_{i + 1} … a_{n - 1} = b_0 b_1 … b_{i - 1} a_i … a_{n - 1} + D. $$
Determine the smallest possible value of $D$.
-/

namespace IMOSL
namespace IMO2023N4

open Finset

/-! ### Extra lemmas -/

theorem prod_range_add_two (n : ℕ) : ∏ x ∈ range n, (x + 2) = (n + 1).factorial := by
  rw [← prod_range_add_one_eq_factorial, prod_range_succ', Nat.mul_one]

theorem prod_range_add_two_mul_Ico_succ (h : i ≤ n) :
    (range i).prod (· + 2) * (Ico i n).prod Nat.succ = (i + 1) * n.factorial := by
  rw [← prod_range_add_one_eq_factorial, prod_range_add_two, Nat.factorial_succ,
    Nat.mul_assoc,  ← prod_range_add_one_eq_factorial, prod_range_mul_prod_Ico _ h]




/-! ### Start of the problem -/

structure goodSeq (n : ℕ) where
  a : ℕ → ℕ
  a_pos : ∀ i, 0 < a i
  b : ℕ → ℕ
  b_pos : ∀ i, 0 < b i
  D : ℕ
  D_pos : 0 < D
  spec : ∀ i < n, (range (i + 1)).prod b * (Ico (i + 1) n).prod a
    = (range i).prod b * (Ico i n).prod a + D


def linear_goodSeq (n : ℕ) : goodSeq n where
  a := Nat.succ
  a_pos := Nat.succ_pos
  b := (· + 2)
  b_pos := (Nat.add_pos_right · Nat.two_pos)
  D := n.factorial
  D_pos := n.factorial_pos
  spec := λ i hi ↦ by rw [prod_range_add_two_mul_Ico_succ hi.le,
      prod_range_add_two_mul_Ico_succ hi, Nat.succ_mul]


namespace goodSeq

variable (X : goodSeq n)

lemma a_lt_b (h : i < n) : X.a i < X.b i := by
  have h0 := (Nat.lt_add_of_pos_right X.D_pos).trans_eq (X.spec i h).symm
  rw [prod_range_succ, prod_eq_prod_Ico_succ_bot h, Nat.mul_assoc] at h0
  exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_mul_lt_mul_left h0)

lemma b_sub_a_pos (h : i < n) : 0 < X.b i - X.a i :=
  Nat.sub_pos_of_lt (X.a_lt_b h)

lemma spec_alt (h : i < n) :
    (range i).prod X.b * (Ico (i + 1) n).prod X.a * (X.b i - X.a i) = X.D := by
  rw [Nat.mul_sub]; apply Nat.sub_eq_of_eq_add'
  rw [Nat.mul_right_comm, ← prod_range_succ, X.spec _ h,
    prod_eq_prod_Ico_succ_bot h, Nat.mul_assoc, (X.a i).mul_comm]

lemma prod_a_pos (S : Finset ℕ) : 0 < S.prod X.a :=
  prod_pos λ _ _ ↦ X.a_pos _

lemma prod_b_pos (S : Finset ℕ) : 0 < S.prod X.b :=
  prod_pos λ _ _ ↦ X.b_pos _

lemma mul_sub_eq_mul_sub (h : i + 1 < n) :
    X.a (i + 1) * (X.b i - X.a i) = X.b i * (X.b (i + 1) - X.a (i + 1)) := by
  have h0 := (X.spec_alt (Nat.lt_of_succ_lt h)).trans (X.spec_alt h).symm
  rw [prod_range_succ,  prod_eq_prod_Ico_succ_bot h, ← Nat.mul_assoc,
    Nat.mul_right_comm _ (X.a _), Nat.mul_right_comm _ (X.b _),
    Nat.mul_assoc, Nat.mul_assoc _ (X.b _)] at h0
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (X.prod_b_pos _) (X.prod_a_pos _)) h0

lemma mul_b_sub_a_lt_a (h : i < n) : i * (X.b i - X.a i) < X.a i := by
  induction' i with i i_ih
  · exact (Nat.zero_mul _).trans_lt (X.a_pos 0)
  · have h0 := Nat.lt_of_succ_lt h
    specialize i_ih h0
    apply Nat.lt_of_mul_lt_mul_left (a := X.b i - X.a i)
    calc
      _ = (i * (X.b i - X.a i) + (X.b i - X.a i)) * (X.b (i + 1) - X.a (i + 1)) := by
        rw [Nat.mul_left_comm, ← Nat.mul_assoc, Nat.succ_mul]
      _ < (X.a i + (X.b i - X.a i)) * (X.b (i + 1) - X.a (i + 1)) :=
        Nat.mul_lt_mul_of_pos_right (Nat.add_lt_add_right i_ih _) (X.b_sub_a_pos h)
      _ = X.b i * (X.b (i + 1) - X.a (i + 1)) := by rw [Nat.add_sub_cancel' (X.a_lt_b h0).le]
      _ = _ := by rw [← X.mul_sub_eq_mul_sub h, Nat.mul_comm]

lemma self_lt_a (h : i < n) : i < X.a i :=
  (Nat.le_mul_of_pos_right i (X.b_sub_a_pos h)).trans_lt (X.mul_b_sub_a_lt_a h)

lemma succ_le_a (h : i < n) : i.succ ≤ X.a i :=
  X.self_lt_a h

lemma factorial_le_D : n.factorial ≤ X.D := by
  obtain rfl | hn : n = 0 ∨ 0 < n := n.eq_zero_or_pos
  · exact X.D_pos
  · have h := prod_eq_prod_Ico_succ_bot hn Nat.succ
    rw [Nat.Ico_zero_eq_range, prod_range_add_one_eq_factorial, Nat.one_mul] at h
    rw [← X.spec_alt hn, prod_range_zero, Nat.one_mul, h]
    refine Nat.le_trans ?_ (Nat.le_mul_of_pos_right _ (X.b_sub_a_pos hn))
    exact prod_le_prod' λ i hi ↦ X.succ_le_a (mem_Ico.mp hi).2

end goodSeq





/-- Final solution -/
theorem final_solution (n : ℕ) : IsLeast (Set.range (goodSeq.D (n := n))) n.factorial :=
  ⟨⟨linear_goodSeq n, rfl⟩, λ _ ⟨X, hX⟩ ↦ (X.factorial_le_D).trans_eq hX⟩
