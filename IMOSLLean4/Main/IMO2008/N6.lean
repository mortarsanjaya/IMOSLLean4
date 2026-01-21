/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# IMO 2008 N6 (P3)

Prove that there exists infinitely many positive integers $n$ such that
  $n^2 + 1$ has a prime divisor greater than $2n + \sqrt{2n}$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2008SL.pdf).
Namely, we pick $p ≡ 1 \pmod{8}$, pick $n$ accordingly, and prove the statement
  with $2n + \sqrt{2n}$ replaced with $2n + \sqrt{10n}$.
Our main statement will use $2n + \sqrt{10n}$ instead of $2n + \sqrt{2n}$ as well.

### Notes

The version formalized in `Archive.Imo.Imo2008Q3` in
  [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/Archive/Imo/Imo2008Q3.html),
  at least up to version `4.27.0-rc1`, keeps the bound $2n + \sqrt{2n}$ and
  instead proves that every prime $p > 20$ with $p ≡ 1 \pmod{4}$ works.
The bound $p > 20$ is almost as strict as it can be, except that $p = 17$ also works.
This is the most notable difference in their proof vs. the official solution.

Our implementation adds much more lemmas and avoids the usage of the `Real` type.
We use `Nat.sqrt`, which computes the **floor** of the square root of a natural number.
This does not change the statement to be proved.
-/

namespace IMOSL
namespace IMO2008N6

/-- If `k + m = n`, then `k^2 ≡ m^2 (mod n)`. -/
theorem sq_modeq_sq_of_add_eq (h : k + m = n) : k ^ 2 ≡ m ^ 2 [MOD n] := by
  subst h; refine (Nat.ModEq.refl (k * m)).add_right_cancel ?_
  rw [Nat.pow_two, Nat.pow_two, ← Nat.mul_add, ← Nat.add_mul,
    Nat.ModEq, Nat.mul_mod_left, Nat.add_comm, Nat.mul_mod_right]

/-- If `k ≤ n` and `n ∣ k^2 + c`, then `n ∣ (n - k)^2 + c`. -/
theorem dvd_sub_sq_add_of_le
    {k n : ℕ} (h : k ≤ n) (h0 : n ∣ k ^ 2 + c) : n ∣ (n - k) ^ 2 + c := by
  rw [Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero.mp h0]
  exact (sq_modeq_sq_of_add_eq (Nat.sub_add_cancel h)).add_right c

/-- If there exists an integer `m` such that `n ∣ m^2 + c`,
  then such `m` exist even with the restriction `2m ≤ p`. -/
theorem exists_two_mul_le_of_exists_dvd_sq_add (hnc : ∃ m, n ∣ m ^ 2 + c) :
    ∃ m, 2 * m ≤ n ∧ n ∣ m ^ 2 + c := by
  rcases hnc with ⟨m, hm⟩
  ---- If `n = 0` then `m = 0` is forced and we are done.
  obtain rfl | hn : n = 0 ∨ n > 0 := Nat.eq_zero_or_pos n
  · rw [Nat.zero_dvd, Nat.add_eq_zero_iff] at hm
    exact ⟨0, Nat.le_refl 0, hm.2.symm ▸ Nat.dvd_refl 0⟩
  ---- Pick one such `m`, and WLOG assume that `m < n`.
  wlog hm0 : m < n generalizing m
  · refine this (m % n) ?_ (Nat.mod_lt _ hn.pos)
    simpa only [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Nat.mod_mod] using hm
  ---- If `2m ≤ n` then we are done.
  obtain hm1 | hm1 : 2 * m ≤ n ∨ n ≤ 2 * m := Nat.le_total _ _
  · exact ⟨m, hm1, hm⟩
  ---- If not, then pick `n - m` instead.
  replace hm1 : 2 * (n - m) ≤ n := calc
    _ = n + n - 2 * m := by rw [Nat.mul_sub, Nat.two_mul]
    _ ≤ n + n - n := Nat.sub_le_sub_left hm1 _
    _ = n := Nat.add_sub_cancel _ _
  exact ⟨n - m, hm1, dvd_sub_sq_add_of_le (Nat.le_of_lt hm0) hm⟩

/-- If `p ≡ 1 (mod 4)`, then there exists an integer `n`
  such that `p ≥ 2n` and `p ∣ n^2 + 1`. -/
theorem exists_two_mul_le_and_dvd_sq_add_one (hp : Nat.Prime p) (hp0 : p ≡ 1 [MOD 4]) :
    ∃ n, 2 * n ≤ p ∧ p ∣ n ^ 2 + 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨c, hc⟩ : IsSquare (-1 : ZMod p) := by
    rw [FiniteField.isSquare_neg_one_iff, ZMod.card, hp0]; decide
  replace hc : p ∣ c.val ^ 2 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add_one, Nat.cast_pow,
      ZMod.natCast_val, ZMod.cast_id, sq, ← hc, neg_add_cancel]
  exact exists_two_mul_le_of_exists_dvd_sq_add ⟨c.val, hc⟩

/-- If `n` is odd, then `n^2 ≡ 1 (mod 8)`. -/
theorem sq_modeq_one_eight_of_odd (hn : Odd n) : n ^ 2 ≡ 1 [MOD 8] := by
  replace hn : n % 2 = 1 := Nat.odd_iff.mp hn
  change n ^ 2 % 8 = 1
  ---- WLOG we can assume `n < 8`.
  wlog hn0 : n < 8
  · replace h : n % 8 % 2 = 1 := (Nat.mod_mod_of_dvd _ ⟨4, rfl⟩).trans hn
    rw [Nat.pow_mod, this h (Nat.mod_lt _ (Nat.succ_pos 7))]
  ---- Now just look at all cases of `n`.
  revert hn; revert n; decide

/-- If `p ≡ 1 (mod 8)`, then there exists an integer `n`
  such that `p > 2n + √(10n)` and `p ∣ n^2 + 1`. -/
theorem exists_two_mul_add_sqrt_10_mul_lt_and_dvd_sq_add_one
    (hp : Nat.Prime p) (hp0 : p ≡ 1 [MOD 8]) :
    ∃ n, 2 * n + Nat.sqrt (10 * n) < p ∧ p ∣ n ^ 2 + 1 := by
  have hp1 : Odd p := Nat.odd_iff.mpr (hp0.of_dvd ⟨4, rfl⟩ : p ≡ 1 [MOD 2])
  ---- Pick `n` with `p ≥ 2n` such that `p ∣ n^2 + 1`; we claim that this `n` works.
  obtain ⟨n, hn, hn0⟩ : ∃ n, 2 * n ≤ p ∧ p ∣ n ^ 2 + 1 :=
    exists_two_mul_le_and_dvd_sq_add_one hp (hp0.of_dvd ⟨2, rfl⟩)
  refine ⟨n, ?_, hn0⟩
  ---- From `p ∣ n^2 + 1`, we get `p ∣ (p - 2n)^2 + 4`.
  replace hn0 : p ∣ (2 * n) ^ 2 + 4 := by
    rw [Nat.mul_pow, ← Nat.mul_succ]
    exact Nat.dvd_mul_left_of_dvd hn0 4
  replace hn0 : p ∣ (p - 2 * n) ^ 2 + 4 :=
    dvd_sub_sq_add_of_le hn hn0
  ---- Write `(p - 2n)^2 + 4 = pl`; then `l = 5 (mod 8)` and so `l ≥ 5`.
  rcases hn0 with ⟨l, hl⟩
  have hl0 : l ≡ 5 [MOD 8] := calc
    l = 1 * l := (Nat.one_mul l).symm
    _ ≡ p * l [MOD 8] := hp0.symm.mul_right l
    _ = (p - 2 * n) ^ 2 + 4 := hl.symm
    _ ≡ 1 + 4 [MOD 8] := by
      have h : Odd (p - 2 * n) := (Nat.odd_sub hn).mpr (iff_of_true hp1 (even_two_mul n))
      exact (sq_modeq_one_eight_of_odd h).add_right 4
  replace hl0 : l ≥ 5 := hl0.symm.trans_le (Nat.mod_le _ _)
  ---- In particular, `(p - 2n)^2 > 5(p - 1) ≥ 10n` and we are done.
  have hn0 : 2 * n < p :=
    Nat.lt_of_le_of_ne hn λ h ↦ Nat.not_even_iff_odd.mpr hp1 (h ▸ even_two_mul n)
  replace hl : (2 * n + 1) * 5 < (p - 2 * n) ^ 2 + 5 := calc
    _ ≤ p * l := Nat.mul_le_mul hn0 hl0
    _ = (p - 2 * n) ^ 2 + 4 := hl.symm
    _ < (p - 2 * n) ^ 2 + 5 := Nat.lt_succ_self _
  rw [Nat.succ_mul, Nat.add_lt_add_iff_right, Nat.mul_right_comm, ← Nat.sqrt_lt'] at hl
  exact Nat.add_lt_of_lt_sub' hl

/-- Final solution -/
theorem final_solution (N) :
    ∃ n ≥ N, ∃ p, Nat.Prime p ∧ 2 * n + Nat.sqrt (10 * n) < p ∧ p ∣ n ^ 2 + 1 := by
  ---- We first pick the primes `p` with the condition `p > N^2` and `p ≡ 1 (mod 8)`.
  obtain ⟨p, hp, hp0, hp1⟩ : ∃ p, Nat.Prime p ∧ N ^ 2 < p ∧ p ≡ 1 [MOD 8] :=
    Nat.exists_prime_gt_modEq_one _ (Nat.succ_ne_zero 7)
  ---- Pick `n` such that `2n + √(10n) < p` and `p ∣ n^2 + 1`.
  obtain ⟨n, hnp, hnp0⟩ : ∃ n, 2 * n + Nat.sqrt (10 * n) < p ∧ p ∣ n ^ 2 + 1 :=
    exists_two_mul_add_sqrt_10_mul_lt_and_dvd_sq_add_one hp hp1
  ---- The bound `p > N^2` automatically implies `n ≥ N`.
  have hn : N ^ 2 < n ^ 2 + 1 :=
    Nat.lt_of_lt_of_le hp0 (Nat.le_of_dvd (Nat.succ_pos _) hnp0)
  have hn : n ≥ N := by
    rwa [Nat.lt_succ_iff, Nat.pow_le_pow_iff_left (Nat.succ_ne_zero 1)] at hn
  ---- We are done.
  exact ⟨n, hn, p, hp, hnp, hnp0⟩
