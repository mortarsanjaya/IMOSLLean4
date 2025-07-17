/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Divisors
import IMOSLLean4.Extra.NatSequence.SeqMax
import Mathlib.Tactic.NormNum

/-!
# IMO 2006 N3

For each $n ∈ ℕ$, define
$$ f(n) = \frac{1}{n} \sum_{k = 1}^n \left\lfloor \frac{n}{k} \right\rfloor. $$
1. Prove that $f(n + 1) > f(n)$ infinitely often.
2. Prove that $f(n + 1) < f(n)$ infinitely often.
-/

namespace IMOSL
namespace IMO2006N3

open Finset

/-! ### Theory of `g(n) = ⌊n/1⌋ + ⌊n/2⌋ + … + ⌊n/n⌋` -/

def g (n : ℕ) : ℕ := (range n).sum λ k ↦ n / (k + 1)

theorem g_zero : g 0 = 0 := rfl

theorem g_succ (n : ℕ) : g n.succ = g n + n.succ.divisors.card := by
  rw [g, g, Nat.divisors]; simp only [Nat.succ_div]
  rw [card_filter, sum_Ico_eq_sum_range, Nat.add_sub_cancel,
    sum_add_distrib, sum_range_succ, Nat.div_eq_of_lt n.lt_succ_self]
  exact congrArg _ (by simp only [add_comm 1])

theorem g_eq_sum_divisors_card : ∀ n : ℕ, g n = (range n).sum λ k ↦ k.succ.divisors.card
  | 0 => by rw [sum_range_zero, g_zero]
  | n + 1 => by rw [g_succ, sum_range_succ, ← g_eq_sum_divisors_card]

theorem two_le_card_divisors {n : ℕ} (h : 2 ≤ n) : 2 ≤ n.divisors.card := by
  rw [← Nat.insert_self_properDivisors (Nat.ne_zero_of_lt h), Nat.succ_le_iff,
    card_insert_of_notMem Nat.self_notMem_properDivisors, Nat.succ_lt_succ_iff, card_pos]
  exact ⟨1, Nat.one_mem_properDivisors_iff_one_lt.mpr h⟩

theorem two_mul_lt_g : ∀ n : ℕ, 6 ≤ n → 2 * n < g n := by
  refine Nat.le_induction (by norm_num : 12 < 14) λ n h h0 ↦ ?_
  rw [Nat.mul_succ, g_succ]
  exact add_lt_add_of_lt_of_le h0 <| two_le_card_divisors <|
    Nat.succ_le_succ (Nat.one_le_of_lt h)

theorem card_divisors_prime {p : ℕ} (hp : p.Prime) : p.divisors.card = 2 :=
  (congr_arg card hp.divisors).trans (card_pair hp.ne_one.symm)





/-! ### Theory of `f(n) = g(n)/n` -/

/-- `f(n) = g(n)/n`, as a rational. -/
def f (n : ℕ) : ℚ := ((g n : ℤ) : ℚ) / ((n : ℤ) : ℚ)

theorem exists_lt_card_divisor_succ (c : ℕ) : ∃ n : ℕ, c < n.succ.divisors.card := by
  refine ⟨2 ^ c - 1, ?_⟩
  rw [Nat.succ_eq_add_one, Nat.sub_add_cancel Nat.one_le_two_pow,
    Nat.divisors_prime_pow Nat.prime_two, card_map, card_range, Nat.lt_succ_iff]

theorem f_lt_f_of_g (h : g a * b < g b * a) : f a < f b := by
  unfold f; rcases a with _ | a
  · rw [g_zero, zero_mul, mul_zero] at h; exact absurd rfl h.ne
  rcases b with _ | b
  · rw [g_zero, zero_mul, mul_zero] at h; exact absurd rfl h.ne
  · have X (n : ℕ) : 0 < (n.succ : ℤ) := Int.natCast_pos.mpr n.succ_pos
    rw [Rat.div_lt_div_iff_mul_lt_mul (X a) (X b), ← Nat.cast_mul, ← Nat.cast_mul]
    exact Int.ofNat_lt.mpr h

theorem f_self_lt_f_succ_of_divisors_card (h : n ≠ 0)
    (h0 : ∀ k < n, k.succ.divisors.card < n.succ.divisors.card) : f n < f n.succ := by
  apply f_lt_f_of_g
  rw [Nat.mul_succ, g_succ, add_mul, add_lt_add_iff_left, g_eq_sum_divisors_card]
  calc _ < (range n).sum λ _ ↦ n.succ.divisors.card :=
        sum_lt_sum_of_nonempty (nonempty_range_iff.mpr h) (λ k h1 ↦ h0 k (mem_range.mp h1))
       _ = n.succ.divisors.card * n := by
        rw [sum_const, card_range, nsmul_eq_mul, mul_comm, Nat.cast_id]

theorem f_succ_lt_self_of_succ_prime_large (h : 6 ≤ n) (h0 : n.succ.Prime) :
    f n.succ < f n := by
  apply f_lt_f_of_g
  rw [g_succ, card_divisors_prime h0, add_mul, Nat.mul_succ, add_lt_add_iff_left]
  exact two_mul_lt_g n h





/-! ### Final solution -/

/-- Final solution, part 1 -/
theorem final_solution_part1 : {n : ℕ | f n < f n.succ}.Infinite := by
  refine Set.infinite_of_forall_exists_gt λ N ↦ ?_
  obtain ⟨n, h0, h1⟩ : ∃ n : ℕ, N < n ∧
      ∀ k : ℕ, k < n → k.succ.divisors.card < n.succ.divisors.card := by
    obtain ⟨K, h0⟩ : ∃ K : ℕ, ∀ k : ℕ, k ≤ N → k.succ.divisors.card ≤ K :=
      ⟨Extra.seqMax (λ n ↦ n.succ.divisors.card) N,
      λ _ ↦ Extra.le_seqMax_of_le (λ n ↦ n.succ.divisors.card)⟩
    have h1 := exists_lt_card_divisor_succ K
    exact ⟨Nat.find h1,
      (Nat.lt_find_iff h1 _).mpr λ k h2 ↦ (h0 k h2).not_gt,
      λ k h2 ↦ (le_of_not_gt (Nat.find_min h1 h2)).trans_lt (Nat.find_spec h1)⟩
  exact ⟨n, f_self_lt_f_succ_of_divisors_card (Nat.ne_zero_of_lt h0) h1, h0⟩

/-- Final solution, part 2 -/
theorem final_solution_part2 : {n : ℕ | f n.succ < f n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt λ N ↦ ?_
  obtain ⟨n, h, h0, h1⟩ : ∃ n, 6 ≤ n ∧ n.succ.Prime ∧ N < n := by
    rcases (max 6 (N + 1) + 1).exists_infinite_primes with ⟨_ | n, h, h0⟩
    · exact absurd h0 Nat.not_prime_zero
    · rw [Nat.add_le_add_iff_right, max_le_iff] at h
      exact ⟨n, h.1, h0, h.2⟩
  exact ⟨n, f_succ_lt_self_of_succ_prime_large h h0, h1⟩
