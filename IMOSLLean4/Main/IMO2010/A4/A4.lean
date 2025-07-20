/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Int.Bitwise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# IMO 2010 A4

Define the sequence $(x_n)_{n ≥ 0}$ recursively by $x_0 = 1$,
  $x_{2k} = (-1)^k x_k$, and $x_{2k + 1} = -x_k$ for all $k ∈ ℕ$.
Prove that for any $n ∈ ℕ$, $$ \sum_{i < n} x_i ≥ 0. $$

**Extra**: Prove that equality holds if and only if the
  base $4$ representation of $n$ only contains $0$ and $2$ as a digit.

### Further directions

I think the proof codes can still be cleaned up.
Another idea is to define the auxiliary functions `List Bool → Bool`
  representing the sequence $(x_n)$ and $(S_n)$.
-/

namespace IMOSL
namespace IMO2010A4

open Finset


/-! ### The sequence `(x_n)_{n ≥ 0}` -/

abbrev x : ℕ → Bool := Nat.binaryRec false λ bit k ↦ xor (bit || k.bodd)

theorem x_zero : x 0 = false :=
  Nat.binaryRec_zero false λ bit k ↦ xor (bit || k.bodd)

theorem x_mul2 (k : ℕ) : x (2 * k) = xor k.bodd (x k) :=
  Nat.binaryRec_eq false k (Or.inl rfl)

theorem x_mul2_add1 (k : ℕ) : x (2 * k + 1) = !x k := by
  apply (Nat.binaryRec_eq true k (Or.inl rfl)).trans
  rw [Bool.true_or, Bool.true_xor]

theorem x_mul4 (k : ℕ) : x (4 * k) = xor k.bodd (x k) := by
  rw [Nat.mul_assoc 2 2, x_mul2, x_mul2, Nat.bodd_mul,
    Nat.bodd_two, Bool.false_and, Bool.false_xor]

theorem x_mul4_add1 (k : ℕ) : x (4 * k + 1) = !x (4 * k) := by
  rw [Nat.mul_assoc 2 2, x_mul2, x_mul2_add1, Nat.bodd_mul,
    Nat.bodd_two, Bool.false_and, Bool.false_xor]

theorem x_mul4_add2 (k : ℕ) : x (4 * k + 2) = x k := by
  rw [Nat.mul_assoc 2 2, ← Nat.mul_succ, x_mul2, x_mul2_add1, Nat.bodd_succ, Nat.bodd_mul,
    Nat.bodd_two, Bool.false_and, Bool.not_false, Bool.true_xor, Bool.not_not]

theorem x_mul4_add3 (k : ℕ) : x (4 * k + 3) = x k := by
  show x (2 * 2 * k + 2 + 1) = x k
  rw [Nat.mul_assoc, ← Nat.mul_succ, x_mul2_add1, x_mul2_add1, Bool.not_not]





/-! ### The series `∑ x_i` -/

abbrev S (n : ℕ) : ℤ := (range n).sum λ k ↦ cond (x k) (-1) 1

theorem S_zero : S 0 = 0 := rfl

theorem S_succ (a : ℕ) : S a.succ = S a + cond (x a) (-1) 1 :=
  sum_range_succ _ a

theorem S_mul4_add2 (k : ℕ) : S (4 * k + 2) = S (4 * k) := by
  rw [S_succ, S_succ, add_assoc, add_eq_left, x_mul4_add1]
  exact (x (4 * k)).recOn rfl rfl

theorem S_mul4 : ∀ k : ℕ, S (4 * k) = 2 * S k :=
  Nat.rec rfl λ k h ↦ by
    change S (4 * k + 4) = 2 * S k.succ
    rw [S_succ, x_mul4_add3, S_succ, x_mul4_add2, S_mul4_add2,
      h, add_assoc, ← two_mul, ← mul_add, ← S_succ]

theorem S_parity : ∀ k : ℕ, (S k).bodd = k.bodd :=
  Nat.rec rfl λ k h ↦ by
    rw [Nat.bodd_succ, S_succ, Int.bodd_add, h, ← Bool.xor_true]
    exact (x k).rec rfl rfl

theorem S_four_mul_add_eq_zero_iff (q : ℕ) {r : ℕ} (h : r < 4) :
    S (4 * q + r) = 0 ↔ S q = 0 ∧ (r = 0 ∨ r = 2) := by
  refine ⟨fun h0 ↦ (and_iff_right_of_imp ?_).mpr ?_, fun h0 ↦ ?_⟩
  ---- If `S_{4q + r} = 0` and `r ∈ {0, 2}`, then `S_q = 0`
  replace h : (2 : ℤ) ≠ 0 := two_ne_zero
  rintro (rfl | rfl)
  · rwa [add_zero, S_mul4, mul_eq_zero, or_iff_right h] at h0
  · rwa [S_mul4_add2, S_mul4, mul_eq_zero, or_iff_right h] at h0
  ---- If `S_{4q + r} = 0`, then `r ∈ {0, 2}`
  replace h0 := congrArg Int.bodd h0
  rw [Int.bodd_zero, S_parity, Nat.bodd_add, Nat.bodd_mul] at h0
  change xor (false && q.bodd) r.bodd = false at h0
  iterate 3 rw [Nat.lt_succ_iff_lt_or_eq] at h
  rw [Nat.lt_one_iff, or_assoc, or_or_or_comm] at h
  revert h; refine (or_iff_left ?_).mp
  rintro (rfl | rfl) <;> exact Bool.true_eq_false_eq_False h0
  ---- If `S_q = 0` and `r ∈ {0, 2}`, then `S_{4q + r} = 0`
  rcases h0 with ⟨h0, rfl | rfl⟩
  · rw [add_zero, S_mul4, h0]; rfl
  · rw [S_mul4_add2, S_mul4, h0]; rfl





/-! ## Final solution -/

/-- Final solution -/
theorem final_solution : ∀ k : ℕ, 0 ≤ S k := by
  ---- Reduce to showing that `x_k = ff` whenever `S_k = 0`
  suffices ∀ k, S k = 0 → x k = false by
    refine Nat.rec (Int.le_refl 0) (λ k h ↦ ?_)
    rw [le_iff_lt_or_eq, Int.lt_iff_add_one_le, zero_add, or_comm] at h
    rw [S_succ]; rcases h with h | h
    · rw [← h, zero_add, this k h.symm]
      exact Int.zero_lt_one.le
    · rw [← Int.add_right_neg 1]
      exact add_le_add h ((x k).rec (neg_le_self zero_le_one) (-1).le_refl)
  ---- Now show that `x_k = ff` whenever `S_k = 0`, using strong induction
  intro k h; induction' k using Nat.strong_induction_on with k k_ih
  obtain ⟨q, r, h0, rfl⟩ : ∃ q r : ℕ, r < 4 ∧ 4 * q + r = k :=
    ⟨k / 4, k % 4, Nat.mod_lt k four_pos, Nat.div_add_mod k 4⟩
  rw [S_four_mul_add_eq_zero_iff q h0, or_comm] at h
  clear h0; rcases h with ⟨h, rfl | rfl⟩
  · rw [x_mul4_add2]
    exact k_ih q (lt_add_of_le_of_pos (Nat.le_mul_of_pos_left _ four_pos) two_pos) h
  rcases q.eq_zero_or_pos with (rfl | h0)
  rw [add_zero, MulZeroClass.mul_zero, x_zero]
  replace k_ih := k_ih q (lt_mul_left h0 <| Nat.succ_lt_succ <| Nat.succ_pos 2) h
  replace h : q.bodd = false := by simpa [S_parity] using congrArg Int.bodd h
  rw [add_zero, x_mul4, h, k_ih]; rfl

/-- Final solution for the extra part -/
theorem final_solution_extra (k : ℕ) :
    S k = 0 ↔ ∀ c ∈ Nat.digits 4 k, c = 0 ∨ c = 2 := by
  induction' k using Nat.strong_induction_on with k k_ih
  obtain ⟨q, r, h, rfl⟩ : ∃ q r : ℕ, r < 4 ∧ 4 * q + r = k :=
    ⟨k / 4, k % 4, Nat.mod_lt k four_pos, Nat.div_add_mod k 4⟩
  rw [S_four_mul_add_eq_zero_iff q h]
  rcases q.eq_zero_or_pos with (rfl | h0)
  ---- Case 1: `q = 0`
  · rw [S_zero, eq_self_iff_true, true_and, MulZeroClass.mul_zero, zero_add]
    rcases r.eq_zero_or_pos with (rfl | h0)
    rw [eq_self_iff_true, true_or, true_iff, Nat.digits_zero]
    intro c h0; exact absurd h0 List.not_mem_nil
    rw [Nat.digits_def' (Nat.succ_lt_succ <| Nat.succ_pos 2) h0,
      Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, Nat.digits_zero]
    simp only [List.mem_singleton]; rw [forall_eq]
  ---- Case 2: `0 < q`
  · have h1 : 1 < 4 := Nat.succ_lt_succ (Nat.succ_pos 2)
    specialize k_ih q (Nat.lt_add_right _ (lt_mul_left h0 h1))
    rw [k_ih, add_comm, Nat.digits_add 4 h1 r q h (Or.inr h0.ne.symm)]
    simp only [List.mem_cons]; rw [forall_eq_or_imp, and_comm]
