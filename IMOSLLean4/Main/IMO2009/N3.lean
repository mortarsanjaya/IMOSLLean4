/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.Group.Unbundled.Int

/-!
# IMO 2009 N3

Let $f : ℕ → ℤ$ be a non-constant function such that
  $a - b ∣ f(a) - f(b)$ for any $a, b ∈ ℕ$.
Prove that there exists infinitely many primes $p$ dividing $f(c)$ for some $c ∈ ℕ$.

### Solution

We follow a modified version of Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
Note that the domain of our function is $ℕ$ rather than $ℕ⁺$.
Solution 1 of the official solution first shows that $f(a + 1) = f(1)$ for
  infinitely many positive integers $a$ and then use that to finish.
Our translation would be $f(a) = f(0)$ for infinitely many $a ∈ ℕ$.
This is also the step that we modify, as follows.

Arguing by contradiction, we assume that there are only finitely many such primes.
Then there exists $K > 0$ such that every prime $p ≥ K$
  does not divide $f(c)$ for any $c ∈ ℕ$.
We claim that $f(kN) = f(0)$ for all $k ∈ ℕ$, where $N = 4K! |f(0)|$.
Note that $f(0) ≠ 0$, as otherwise we already obtain a contradiction.

To prove the claim, first note that $N ∣ f(kN) - f(0)$.
Thus $f(0) ∣ f(kN)$ and $4K! ∣ f(kN)/f(0) - 1$.
In particular, every prime less than $K$ do not divide $f(kN)/f(0)$.
On the other hand, by assumption, every prime greater than or
  equal to $K$ do not divide $f(kN)$ either.
Thus $f(kN)/f(0) = ±1$, and then fact that $4 ∣ f(kN)/f(0) - 1$ yields $f(kN)/f(0) = 1$.
This proves the claim.

The rest is the same as the official solution.
-/

namespace IMOSL
namespace IMO2009N3

variable {f : ℕ → ℤ} (hf : ∀ a b : ℕ, (a : ℤ) - b ∣ f a - f b)
include hf

/-- If only finitely many primes divide `f(c)` for some `c`, then `f` is constant. -/
lemma const_of_finite_prime_divisor (hf0 : ∀ p ≥ K, Nat.Prime p → (∀ c, ¬(p : ℤ) ∣ f c)) :
    ∃ C, ∀ x, f x = C := by
  ---- First note that `f(0) ≠ 0`; else infinitely many primes divide `f(0)`.
  have hf1 : f 0 ≠ 0 := by
    obtain ⟨p, hpK, hp⟩ : ∃ p ≥ K, Nat.Prime p := Nat.exists_infinite_primes K
    exact λ h ↦ hf0 p hpK hp 0 (h ▸ Int.dvd_zero _)
  ---- We show that `f(kN) = f(0)` for all `k`, where `N = 4K! |f(0)|`.
  let N : ℕ := 4 * K.factorial * (f 0).natAbs
  have hN : N > 0 :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos 3) (Nat.factorial_pos K)) (Int.natAbs_pos.mpr hf1)
  have hN0 (k) : f (k * N) = f 0 := by
    -- First, note that `f(0) ∣ f(kN)` and `4K! ∣ M - 1`, where `M = f(kN)/f(0)`.
    have h : ((4 * K.factorial : ℕ) : ℤ) * f 0 ∣ f (k * N) - f 0 := calc
      _ ∣ (k * (4 * K.factorial : ℕ) : ℤ) * (f 0).natAbs :=
        Int.mul_dvd_mul ⟨k, Int.mul_comm _ _⟩ Int.dvd_natAbs_self
      _ = ((k * N : ℕ) : ℤ) := by rw [← Int.natCast_mul, ← Int.natCast_mul, Nat.mul_assoc]
      _ ∣ f (k * N) - f 0 := hf _ _
    obtain ⟨M, hM⟩ : f 0 ∣ f (k * N) := calc
      _ ∣ f (k * N) - f 0 + f 0 := Int.dvd_add (dvd_of_mul_left_dvd h) (Int.dvd_refl _)
      _ = f (k * N) := Int.sub_add_cancel _ _
    replace h : ((4 * K.factorial : ℕ) : ℤ) ∣ M - 1 := by
      refine Int.dvd_of_mul_dvd_mul_right hf1 ?_
      rwa [Int.sub_mul, Int.one_mul, Int.mul_comm M, ← hM]
    -- Next, we show that `M = ±1`...
    obtain rfl | rfl : M = 1 ∨ M = -1 := by
      rw [← Int.natAbs_eq_natAbs_iff, Int.natAbs_one, Nat.eq_one_iff_not_exists_prime_dvd]
      -- ... via showing that no primes divide `M`.
      intro p hp hpM
      replace hpM : (p : ℤ) ∣ M := Int.natCast_dvd.mpr hpM
      obtain hpK | hpK : p ≥ K ∨ p ≤ K := Nat.le_total _ _
      -- If `p ≥ K` then `p ∤ f(kN) = f(0) M` implies `p ∤ M`.
      · refine hf0 p hpK hp (k * N) ?_
        calc (p : ℤ)
          _ ∣ M := hpM
          _ ∣ f 0 * M := Int.dvd_mul_left _ _
          _ = f (k * N) := hM.symm
      -- If `p ≤ K` then `p ∣ K!` implies `p ∣ M - 1` and so `p ∤ M`.
      · replace h : (p : ℤ) ∣ M - 1 := calc
          _ ∣ (K.factorial : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial hp.pos hpK)
          _ ∣ ((4 * K.factorial : ℕ) : ℤ) := ⟨4, by rw [Int.natCast_mul, Int.mul_comm]; rfl⟩
          _ ∣ M - 1 := h
        rw [Int.dvd_iff_dvd_of_dvd_sub h, Int.natCast_dvd] at hpM
        exact hp.not_dvd_one hpM
    -- If `M = 1` then we are done.
    · rw [hM, Int.mul_one]
    -- If `M = -1`, contradiction from `4 ∣ M - 1`.
    · replace h : (4 : ℤ) ∣ -2 := calc
        _ ∣ ((4 * K.factorial : ℕ) : ℤ) := ⟨K.factorial, Int.natCast_mul _ _⟩
        _ ∣ -1 - 1 := h
      exact absurd h (by decide)
  ---- Now fix `a ∈ ℕ` and choose some `b > |f(a) - f(0)| + a`.
  refine ⟨f 0, λ a ↦ ?_⟩
  obtain ⟨b, hb⟩ : ∃ b, b > (f a - f 0).natAbs + a :=
    ⟨(f a - f 0).natAbs + a + 1, Nat.lt_add_one _⟩
  ---- Then `bN - a ∣ f(bN) - f(a) = f(0) - f(a)` implies `f(a) = f(0)`.
  replace hb : |f 0 - f a| < (b * N : ℕ) - a := by
    rw [abs_sub_comm, lt_sub_iff_add_lt, ← Int.natCast_natAbs, ← Int.natCast_add, Int.ofNat_lt]
    exact hb.trans_le (Nat.le_mul_of_pos_right b hN)
  have hb0 : ((b * N : ℕ) : ℤ) - a ∣ f 0 - f a := hN0 b ▸ hf _ _
  exact (Int.eq_of_sub_eq_zero (Int.eq_zero_of_abs_lt_dvd hb0 hb)).symm

/-- Final solution -/
theorem final_solution (hf0 : ∀ C, ∃ x, f x ≠ C) (K : ℕ) :
    ∃ p ≥ K, Nat.Prime p ∧ ∃ c, (p : ℤ) ∣ f c := by
  contrapose! hf0; exact const_of_finite_prime_divisor hf hf0
