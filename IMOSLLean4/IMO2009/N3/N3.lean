/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Prime.Infinite

/-!
# IMO 2009 N3

Let $f : ℕ → ℤ$ be a non-constant function such that
  $a - b ∣ f(a) - f(b)$ for any $a, b ∈ ℕ$.
Prove that there exists infinitely many primes $p$
  that divide $f(c)$ for some $c ∈ ℕ$.

### Notes

In this file, the infinitude of such primes is rephrased as follows:
  for any $k ∈ ℕ$, there exists a prime $p ≥ k$ such that
  $p ∣ f(c)$ for some $c ∈ ℕ$.
The equivalence is clear, and this avoids importing `Mathlib.Data.Set.Finite`.
-/

namespace IMOSL
namespace IMO2009N3

variable {f : ℕ → ℤ} (h : ∀ a b : ℕ, (a : ℤ) - b ∣ f a - f b)
include h

lemma const_of_infinite_map_eq_map_zero (h0 : ∀ k, ∃ n, k ≤ n ∧ f n = f 0) :
    ∃ C, f = λ _ ↦ C := by
  refine ⟨f 0, funext λ b ↦ ?_⟩
  obtain ⟨n, h0, h1⟩ := h0 (b + (f 0 - f b).natAbs + 1)
  specialize h n b
  rw [Nat.succ_le_iff, lt_iff_exists_add] at h0
  rcases h0 with ⟨C, h0, rfl⟩
  rw [h1, add_assoc, Nat.cast_add, add_sub_cancel_left, Int.natCast_dvd] at h
  have h2 := Nat.eq_zero_of_dvd_of_lt h (Nat.lt_add_of_pos_right h0)
  rwa [Int.natAbs_eq_zero, sub_eq_zero, eq_comm] at h2

lemma const_of_finite_prime_divisor (h0 : ∀ p : ℕ, p.Prime → (∃ c, (p : ℤ) ∣ f c) → p < K) :
    ∃ C, f = λ _ ↦ C := by
  have h1 : f 0 ≠ 0 := λ h1 ↦ by
    obtain ⟨p, h2, h3⟩ := K.exists_infinite_primes
    exact h2.not_gt (h0 p h3 ⟨0, 0, h1⟩)
  refine const_of_infinite_map_eq_map_zero h
    λ k ↦ ⟨(f 0).natAbs * (4 * K.factorial) * k, ?_, ?_⟩
  ---- `k ≤ Nk`, where `N = |f(0)| ⬝ 4K!`
  · exact Nat.le_mul_of_pos_left _ <| Nat.mul_pos (Int.natAbs_pos.mpr h1)
      (Nat.mul_pos (Nat.succ_pos 3) K.factorial_pos)
  ---- `f(kN) = f(0)`
  · specialize h ((f 0).natAbs * (4 * K.factorial) * k) 0
    rw [Nat.cast_zero, Int.sub_zero, Nat.cast_mul] at h
    apply (dvd_mul_right _ _).trans at h
    rw [Nat.cast_mul, ← abs_dvd, Int.natCast_natAbs,
      abs_mul, abs_abs, ← abs_mul, abs_dvd] at h
    obtain ⟨m, h2⟩ := dvd_sub_self_right.mp (dvd_of_mul_right_dvd h)
    rw [h2, ← mul_sub_one, mul_dvd_mul_iff_left h1, Int.natCast_dvd] at h
    rw [h2, mul_right_eq_self₀, or_iff_left h1]
    clear h1; by_cases h1 : m.natAbs = 1
    -- Case 1: `|m| = 1`
    · rw [Int.natAbs_eq_iff, Nat.cast_one] at h1
      exact h1.resolve_right λ h1 ↦ absurd ((dvd_mul_right _ _).trans (h1 ▸ h))
        (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos 1) (Nat.le_succ 3))
    -- Case 2: `|m| ≠ 1`
    · apply Nat.exists_prime_and_dvd at h1; rcases h1 with ⟨p, h1, h3⟩
      specialize h0 p h1 ⟨(f 0).natAbs * (4 * Nat.factorial K) * k,
        h2 ▸ dvd_mul_of_dvd_right (Int.natCast_dvd.mpr h3) _⟩
      replace h := (Nat.dvd_factorial h1.pos h0.le).trans (dvd_of_mul_left_dvd h)
      rw [← Int.natCast_dvd] at h h3
      exact absurd (Int.natCast_dvd.mp <|
        (Int.dvd_iff_dvd_of_dvd_sub h).mp h3) h1.not_dvd_one



/-- Final solution -/
theorem final_solution (h0 : ∀ C : ℤ, ∃ b : ℕ, f b ≠ C) (K : ℕ) :
    ∃ p : ℕ, K ≤ p ∧ p.Prime ∧ ∃ c, (p : ℤ) ∣ f c := by
  refine by_contra λ h1 ↦ absurd h0 (not_forall.mpr ⟨f 0, ?_⟩)
  obtain ⟨C, rfl⟩ : ∃ C, f = λ _ ↦ C :=
    const_of_finite_prime_divisor h (K := K) λ p h2 h3 ↦
      lt_of_not_ge λ h4 ↦ not_exists.mp h1 p ⟨h4, h2, h3⟩
  rintro ⟨b, hb⟩; exact hb rfl
