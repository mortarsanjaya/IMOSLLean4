/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Bits

/-!
# IMO 2009 N2

For each positive integer $n$, let $Ω(n)$ denote the number of
  prime factors of $n$, counting multiplicity.
For convenience, we denote $Ω(0) = 0$.
1. Prove that for any $N ∈ ℕ$, there exists $a, b ∈ ℕ$ distinct
    such that $Ω((a + k)(b + k))$ is even for all $k < N$.
2. Prove that for any $a, b ∈ ℕ$, if $Ω((a + k)(b + k))$ is even
    for all $k ∈ ℕ$, then $a = b$.
-/

namespace IMOSL
namespace IMO2009N2

open ArithmeticFunction

/-! ### Part 1 -/

lemma Even_iff_bodd {k : ℕ} : Even k ↔ k.bodd = false := by
  rw [Nat.even_iff, Nat.mod_two_of_bodd, Bool.toNat_eq_zero]

/-- Final solution, part 1 -/
theorem final_solution_part1 (N) : ∃ a b, a ≠ b ∧ ∀ k < N, Even (Ω ((a + k) * (b + k))) := by
  ---- First choose `a` and `b` via a map from `ℕ` to `Fin N → Bool`
  let f : ℕ → Fin N → Bool := λ a k ↦ (Ω (a.succ + k)).bodd
  have h : ¬f.Injective := not_injective_infinite_finite f
  rw [Function.Injective] at h; simp_rw [not_forall] at h
  rcases h with ⟨a, b, h, h0⟩
  refine ⟨a.succ, b.succ, Nat.succ_ne_succ.mpr h0, λ k h1 ↦ ?_⟩
  ---- Now prove that such `a` and `b` works
  have X (c : ℕ) : c.succ + k ≠ 0 := c.succ_add k ▸ (c + k).succ_ne_zero
  rw [Even_iff_bodd, cardFactors_mul (X _) (X _), Nat.bodd_add, bne_eq_false_iff_eq]
  exact congr_fun h ⟨k, h1⟩





/-! ### Part 2 -/

lemma eventually_const_of_map_succ_eq {f : ℕ → α} (h : ∀ k, a ≤ k → f k = f k.succ) :
    ∀ k m, a ≤ k → a ≤ m → f k = f m :=
  suffices ∀ k, a ≤ k → f k = f a
    from λ k m hk hm ↦ (this k hk).trans (this m hm).symm
  Nat.le_induction rfl λ k h0 ↦ (h k h0).symm.trans

lemma exists_lt_omega_bodd_ne_succ (a) : ∃ b, a ≤ b ∧ (Ω b).bodd ≠ (Ω b.succ).bodd := by
  by_contra h; simp only [not_exists, not_and, not_not] at h
  rcases a.exists_infinite_primes with ⟨p, h0, h1⟩
  apply absurd (eventually_const_of_map_succ_eq h
    p (p * p) h0 (h0.trans (Nat.le_mul_self p)))
  rw [cardFactors_apply_prime h1, ← sq, cardFactors_apply_prime_pow h1]
  trivial

/-- Final solution, part 2 -/
theorem final_solution_part2 (h : ∀ k, Even (Ω ((a + k) * (b + k)))) : a = b := by
  wlog h0 : a ≤ b
  · exact (this (λ k ↦ Nat.mul_comm _ _ ▸ h k) (Nat.le_of_not_ge h0)).symm
  rw [le_iff_exists_add] at h0; rcases h0 with ⟨_ | c, rfl⟩; rfl
  rcases exists_lt_omega_bodd_ne_succ a.succ with ⟨b, h0, h1⟩
  revert h1; apply absurd
  specialize h (a * c + (b - a) * c.succ)
  rw [Even_iff_bodd, add_right_comm, ← add_assoc, a.add_comm, ← Nat.mul_succ,
    ← add_mul, Nat.add_sub_of_le (a.le_succ.trans h0), ← Nat.succ_mul] at h
  replace h0 := (Nat.zero_lt_of_lt h0).ne.symm
  have h1 := b.succ_ne_zero
  have h2 := c.succ_ne_zero
  rwa [cardFactors_mul (Nat.mul_ne_zero h0 h2) (Nat.mul_ne_zero h1 h2),
    cardFactors_mul h0 h2, cardFactors_mul h1 h2, Nat.bodd_add,
    bne_eq_false_iff_eq, Nat.bodd_add, Nat.bodd_add, Bool.xor_left_inj] at h
