/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Int.Basic

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
Thus $f(kN)/f(0) = ±1$, and the fact that $4 ∣ f(kN)/f(0) - 1$ yields $f(kN)/f(0) = 1$.
This proves the claim.

The rest is the same as the official solution.
-/

namespace IMOSL
namespace IMO2009N3

variable {f : ℕ → ℤ} (hf : ∀ a b : ℕ, (a : ℤ) - b ∣ f a - f b)
include hf

/-- If `f(c) = f(0)` for infinitely many `c`, then `f` is constant. -/
lemma const_of_infinite_map_eq_map_zero (hf0 : ∀ K, ∃ c ≥ K, f c = f 0) :
    ∃ C, ∀ x, f x = C := by
  ---- Fix `a ∈ ℕ`.
  refine ⟨f 0, λ a ↦ ?_⟩
  ---- Choose some `c > |f(a) - f(0)| + a` such that `f(b) = f(0)`.
  obtain ⟨c, hc, hc0⟩ : ∃ c > (f 0 - f a).natAbs + a, f c = f 0 := hf0 _
  ---- Note that `c - a ∣ f(0) - f(a)`.
  replace hc0 : ((c - a : ℕ) : ℤ) ∣ f 0 - f a := by
    rw [← hc0, Int.natCast_sub (Nat.le_of_lt (Nat.lt_of_add_left_lt hc))]
    exact hf c a
  ---- But we also have `|f(0) - f(a)| < c - a`.
  replace hc : (f 0 - f a).natAbs < c - a := Nat.lt_sub_of_add_lt hc
  ---- Thus `f(a) = f(0)`.
  exact (Int.eq_of_sub_eq_zero (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hc0 hc)).symm

/-- If only finitely many primes divide `f(c)` for some `c`, then `f` is constant. -/
lemma const_of_finite_prime_divisor (hf0 : ∀ p ≥ K, Nat.Prime p → (∀ c, ¬(p : ℤ) ∣ f c)) :
    ∃ C, ∀ x, f x = C := by
  ---- First note that `f(0) ≠ 0`; else infinitely many primes divide `f(0)`.
  have hf1 : f 0 ≠ 0 := by
    obtain ⟨p, hpK, hp⟩ : ∃ p ≥ K, Nat.Prime p := Nat.exists_infinite_primes K
    exact λ h ↦ hf0 p hpK hp 0 (h ▸ Int.dvd_zero _)
  ---- Let `N = 4K! f(0)` where `K` is greater than all primes dividing `f(c)` for some `c`.
  let N : ℕ := 4 * K.factorial * (f 0).natAbs
  have hN : N > 0 :=
    have h : 0 < 4 := Nat.succ_pos 3
    Nat.mul_pos (Nat.mul_pos h K.factorial_pos) (Int.natAbs_pos.mpr hf1)
  /- By using `const_of_infinite_map_eq_map_zero`,
    it suffices to prove that `f(kN) = f(0)` for all `k ∈ ℕ`. -/
  suffices ∀ k, f (k * N) = f 0
    from const_of_infinite_map_eq_map_zero hf
      λ m ↦ ⟨m * N, Nat.le_mul_of_pos_right m hN, this m⟩
  ---- First, the given condition on `f` yields `N ∣ f(kN) - f(0)`.
  intro k
  have h : ((4 * K.factorial : ℕ) : ℤ) * f 0 ∣ f (k * N) - f 0 := calc
    _ ∣ (k * (4 * K.factorial : ℕ) : ℤ) * (f 0).natAbs :=
      Int.mul_dvd_mul ⟨k, Int.mul_comm _ _⟩ Int.dvd_natAbs_self
    _ = ((k * N : ℕ) : ℤ) := by rw [← Int.natCast_mul, ← Int.natCast_mul, Nat.mul_assoc]
    _ ∣ f (k * N) - f 0 := hf _ _
  ---- We get `f(0) ∣ f(kN)`; write `M = f(kN)/f(0)`.
  obtain ⟨M, hM⟩ : f 0 ∣ f (k * N) := calc
      _ ∣ f (k * N) - f 0 + f 0 := Int.dvd_add (dvd_of_mul_left_dvd h) (Int.dvd_refl _)
      _ = f (k * N) := Int.sub_add_cancel _ _
  ---- Then `N ∣ f(kN) - f(0)` implies `4K! ∣ M - 1`.
  replace h : ((4 * K.factorial : ℕ) : ℤ) ∣ M - 1 := by
    refine Int.dvd_of_mul_dvd_mul_right hf1 ?_
    rwa [Int.sub_mul, Int.one_mul, Int.mul_comm M, ← hM]
  ---- Next we show that no primes divide `|M|`.
  have hM0 (p) (hp : Nat.Prime p) : ¬p ∣ Int.natAbs M := by
    -- Well, suppose that a prime `p` divides `M`.
    intro hpM
    replace hpM : (p : ℤ) ∣ M := Int.natCast_dvd.mpr hpM
    obtain hpK | hpK : p ≥ K ∨ p ≤ K := Nat.le_total _ _
    -- If `p ≥ K` then `p ∤ f(kN) = f(0) M` yields a contradiction.
    · refine hf0 p hpK hp (k * N) ?_
      calc (p : ℤ)
        _ ∣ M := hpM
        _ ∣ f 0 * M := Int.dvd_mul_left _ _
        _ = f (k * N) := hM.symm
    -- If `p ≤ K` then `p ∣ K!` implies `p ∣ M - 1`; contradiction.
    · replace h : (p : ℤ) ∣ M - 1 := calc
        _ ∣ (K.factorial : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial hp.pos hpK)
        _ ∣ ((4 * K.factorial : ℕ) : ℤ) := ⟨4, by rw [Int.natCast_mul, Int.mul_comm]; rfl⟩
        _ ∣ M - 1 := h
      rw [Int.dvd_iff_dvd_of_dvd_sub h, Int.natCast_dvd] at hpM
      exact hp.not_dvd_one hpM
  ---- Thus we get `M = ±1`.
  replace hM0 : M = 1 ∨ M = -1 := by
    rwa [← Int.natAbs_eq_natAbs_iff, Int.natAbs_one, Nat.eq_one_iff_not_exists_prime_dvd]
  rcases hM0 with rfl | rfl
  ---- If `M = 1` then we are done.
  · rw [hM, Int.mul_one]
  ---- If `M = -1`, contradiction from `4 ∣ M - 1`.
  · replace h : (4 : ℤ) ∣ -2 := calc
      _ ∣ ((4 * K.factorial : ℕ) : ℤ) := ⟨K.factorial, Int.natCast_mul _ _⟩
      _ ∣ -1 - 1 := h
    exact absurd h (by decide : ¬(4 : ℤ) ∣ -2)

/-- Final solution -/
theorem final_solution (hf0 : ∀ C, ∃ x, f x ≠ C) (K : ℕ) :
    ∃ p ≥ K, Nat.Prime p ∧ ∃ c, (p : ℤ) ∣ f c := by
  contrapose! hf0; exact const_of_finite_prime_divisor hf hf0
