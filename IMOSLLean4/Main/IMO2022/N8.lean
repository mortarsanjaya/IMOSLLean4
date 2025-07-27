/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# IMO 2022 N8

Prove that $2^n + 65$ does not divide $5^n - 3^n$ for any positive integer $n$.

### Solution

We follow Solution 2 of the
  [official solution](https://www.imo-official.org/problems/IMO2022SL.pdf).
The solution works with $65$ replaced by any positive integer $N ≡ 5 \pmod{60}$.
-/

namespace IMOSL
namespace IMO2022N8

open scoped NumberTheorySymbols

/-! ### Some lemmas on Jacobi symbols -/

/-- If `a ∈ {0, 1, -1}`, then `a^{2n + 1} = a` for any `n ∈ ℕ`. -/
theorem pow_odd'_eq_self_of_zero_or_one_or_neg_one
    {a : ℤ} (ha : a = 0 ∨ a = 1 ∨ a = -1) (n) :
    a ^ (2 * n + 1) = a := by
  rcases ha with rfl | ha
  · exact Int.mul_zero _
  · rw [Int.pow_succ, pow_mul, sq_eq_one_iff.mpr ha, Int.one_pow, Int.one_mul]

/-- `J(a | b)^{2n + 1} = J(a | b)`. -/
theorem jacobiSym_pow_odd'_eq_self (a b n) : J(a | b) ^ (2 * n + 1) = J(a | b) :=
  pow_odd'_eq_self_of_zero_or_one_or_neg_one (jacobiSym.trichotomy a b) n

/-- `J(a^{2n + 1} | b) = J(a | b)`. -/
theorem jacobiSym_pow_left_odd'_eq_self (a b n) : J(a ^ (2 * n + 1) | b) = J(a | b) :=
  (jacobiSym.pow_left a _ b).trans (jacobiSym_pow_odd'_eq_self a b n)

/-- `J(2 | 5) = -1`. -/
theorem jacobiSym_two_five : J(2 | 5) = -1 :=
  jacobiSym.at_two (Nat.odd_iff.mpr rfl)

/-- If `a ≡ b (mod c)`, then `J(a | c) = J(b | c)`. -/
theorem jacobiSym_of_modeq {a b : ℤ} {c : ℕ} (h : a ≡ b [ZMOD c]) : J(a | c) = J(b | c) := by
  rw [jacobiSym.mod_left, h, ← jacobiSym.mod_left]

/-- If `a ≡ b (mod c)`, then `J(a | c) = J(b | c)`, `ℕ` version. -/
theorem jacobiSym_of_modeq_nat {a b c : ℕ} (h : a ≡ b [MOD c]) : J(a | c) = J(b | c) :=
  jacobiSym_of_modeq (Int.natCast_modEq_iff.mpr h)



/-! ### Start of the problem -/

/-- If `N > 0`, then `5 ≢ 3 (mod 2 + N)`. -/
theorem five_not_modeq_three_mod_two_add_N (hN : 0 < N) : ¬5 ≡ 3 [MOD 2 + N] :=
  ---- `5 ≡ 3 (mod 2 + N)` implies `2 + N ∣ 2`, which is impossible since `N > 0`.
  λ h0 ↦ Nat.not_dvd_of_pos_of_lt Nat.two_pos (Nat.lt_add_of_pos_right hN)
    ((Nat.modEq_iff_dvd' (by norm_num : 3 ≤ 5)).mp h0.symm)

/-- If `N ≡ 2 (mod 3)` and `k > 0`, then `5 ≢ 3 (mod 2 + N)`. -/
theorem twenty_five_pow_not_modeq_nine_mod_four_pow_add_N (hN : N % 3 = 2) (hk : 0 < k) :
    ¬25 ^ k ≡ 9 ^ k [MOD 4 ^ k + N] := by
  ---- First note that `3 ∣ 4^k + N`.
  replace hN : 3 ∣ 4 ^ k + N := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hN, Nat.pow_mod, Nat.one_pow]
  ---- Thus it suffices to work out the congruence modulo `3`.
  suffices ¬25 ^ k ≡ 9 ^ k [MOD 3] from mt (Nat.ModEq.of_dvd hN) this
  ---- Indeed, we have `25 ≢ 9^k (mod 3)`.
  calc 25 ^ k % 3
    _ = 1 := by rw [Nat.pow_mod, Nat.one_pow]
    _ ≠ 0 := Nat.one_ne_zero
    _ = 9 ^ k % 3 := by rw [Nat.pow_mod, Nat.zero_pow hk]

/-- If `N ≡ 5 (mod 60)`, then `5^n ≢ 3^n (mod 2^n + N)` for any `n > 0`. -/
theorem five_pow_not_modeq_three_pow_mod_two_pow_add_N (hn : 0 < n) (hN : N % 60 = 5) :
    ¬5 ^ n ≡ 3 ^ n [MOD 2 ^ n + N] := by
  ---- First solve the case where `n` is even.
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := Nat.even_or_odd' n
  · replace hN : N % 3 = 2 := by rw [← Nat.mod_mod_of_dvd N ⟨20, rfl⟩, hN]
    replace hn : 0 < k := Nat.pos_of_mul_pos_left hn
    rw [Nat.pow_mul, Nat.pow_mul, Nat.pow_mul]
    exact twenty_five_pow_not_modeq_nine_mod_four_pow_add_N hN hn
  ---- Now suppose that `n = 2k + 1` is odd. Next solve the case `k = 0`, `n = 1`.
  obtain rfl | hk : k = 0 ∨ 0 < k := Nat.eq_zero_or_pos k
  · replace hN : 0 < N := calc
      0 < 5 := Nat.succ_pos 4
      _ = N % 60 := hN.symm
      _ ≤ N := Nat.mod_le N 60
    exact five_not_modeq_three_mod_two_add_N hN
  /- Finally, suppose that `n = 2k + 1` with `k > 1`.
    Then by Jacobi symbol computation, `5^n ≡ 3^n (mod 2^n + N)` implies `-1 = 1`. -/
  intro h0
  set n : ℕ := 2 * k + 1
  suffices (-1 : ℤ) = 1 from absurd this (by norm_num)
  calc -1
    _ = J((2 : ℕ) | 5) := jacobiSym_two_five.symm
    _ = J((2 ^ n : ℕ) | 5) := by rw [Int.natCast_pow, jacobiSym_pow_left_odd'_eq_self]
    _ = J((2 ^ n + N : ℕ) | 5) := by
      -- For this step, we need `2^n ≡ 2^n + N (mod 5)`, or `N ≡ 0 (mod 5)`.
      replace hN : N ≡ 0 [MOD 5] := by rw [Nat.ModEq, ← Nat.mod_mod_of_dvd N ⟨12, rfl⟩, hN]
      exact jacobiSym_of_modeq_nat (hN.symm.add_left _)
    _ = J((5 : ℕ) | 2 ^ n + N) := by
      -- For this step, we need `2^n + N` to be odd, or `(2^n + N) % 2 = 1`.
      replace hN : (2 ^ n + N) % 2 = 1 := by
        rw [Nat.pow_succ, Nat.mul_add_mod', ← Nat.mod_mod_of_dvd N ⟨30, rfl⟩, hN]
      exact jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hN) rfl
    _ = J((5 ^ n : ℕ) | 2 ^ n + N) := by
      rw [Int.natCast_pow, jacobiSym_pow_left_odd'_eq_self]
    _ = J((3 ^ n : ℕ) | 2 ^ n + N) := jacobiSym_of_modeq_nat h0
    _ = J((3 : ℕ) | 2 ^ n + N) := by rw [Int.natCast_pow, jacobiSym_pow_left_odd'_eq_self]
    _ = J((2 ^ n + N : ℕ) | 3) := by
      -- For this step, we need `(2^n + N) % 4 = 1`.
      replace hn : 4 ∣ 2 ^ n :=
        Nat.pow_dvd_pow 2 (Nat.succ_le_succ (Nat.mul_pos Nat.two_pos hk))
      replace hN : (2 ^ n + N) % 4 = 1 := by
        rw [← Nat.mod_add_mod, Nat.dvd_iff_mod_eq_zero.mp hn,
          Nat.zero_add, ← Nat.mod_mod_of_dvd N ⟨15, rfl⟩, hN]
      exact jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr rfl) hN
    _ = J((1 : ℕ) | 3) := by
      -- For this step, we need `2^n + N ≡ 1 (mod 3)`, or `(2^n + N) % 3 = 1`.
      replace hN : N % 3 = 2 := by rw [← Nat.mod_mod_of_dvd N ⟨20, rfl⟩, hN]
      replace hN : (2 ^ n + N) % 3 = 1 := by
        rw [Nat.add_mod, hN, Nat.pow_succ, ← Nat.mod_mul_mod,
          Nat.pow_mul, Nat.pow_mod, Nat.one_pow]
      exact jacobiSym_of_modeq_nat hN
    _ = 1 := jacobiSym.one_left 3

/-- Final solution -/
theorem final_solution (hn : 0 < n) : ¬5 ^ n ≡ 3 ^ n [MOD 2 ^ n + 65] :=
  five_pow_not_modeq_three_pow_mod_two_pow_add_N hn rfl
