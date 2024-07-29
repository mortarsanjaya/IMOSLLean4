/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# IMO 2022 N8

Given $n ∈ ℕ$ such that $2^n + 65 ∣ 5^n - 3^n$, prove that $n = 0$.
-/

namespace IMOSL
namespace IMO2022N8

theorem jacobiSym_pow_odd'_eq_self (a : ℤ) (b n : ℕ) :
    jacobiSym a b ^ (2 * n + 1) = jacobiSym a b := by
  rw [pow_succ, pow_mul]
  rcases jacobiSym.trichotomy a b with h | h
  · rw [h, mul_zero]
  · rw [sq_eq_one_iff.mpr h, one_pow, one_mul]

theorem jacobiSym_pow_left_odd'_eq_self (a : ℤ) (b n : ℕ) :
    jacobiSym (a ^ (2 * n + 1)) b = jacobiSym a b := by
  rw [jacobiSym.pow_left, jacobiSym_pow_odd'_eq_self]

/-- Final solution, general version: `N ≡ 5 [mod 60]` -/
theorem final_solution_general (hN : N % 60 = 5) (h : 5 ^ n ≡ 3 ^ n [MOD 2 ^ n + N]) :
    n = 0 := by
  rcases n.even_or_odd' with ⟨_ | k, rfl | rfl⟩
  ---- Case 1: `n = 0`
  · rfl
  ---- Case 2: `n = 1`
  · change 5 ≡ 3 [MOD 2 + N] at h
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (Nat.le_add_left 3 2)] at h
    refine absurd h (Nat.not_dvd_of_pos_of_lt Nat.zero_lt_two (Nat.lt_add_of_pos_right ?_))
    exact (Nat.succ_pos 4).trans_le (hN.symm.trans_le (N.mod_le 60))
  ---- Case 3: `n = 2k` with `k > 0`
  · replace hN : N % 3 = 2 := by
      rw [← Nat.mod_mod_of_dvd N ⟨20, rfl⟩, hN]
    replace hN : 3 ∣ 2 ^ (2 * (k + 1)) + N := by
      have h0 : 2 ^ 2 % 3 = 1 := by rfl
      rw [Nat.dvd_iff_mod_eq_zero, pow_mul, Nat.add_mod, hN, Nat.pow_mod, h0, one_pow]; rfl
    replace h : _ % 3 = _ % 3 := h.of_dvd hN
    replace hN : 5 ^ 2 % 3 = 1 := by rfl
    rw [Nat.pow_mul, Nat.pow_mod, hN, one_pow,
      Nat.mul_succ, Nat.pow_succ, Nat.mul_mod_left] at h
    exact absurd h Nat.one_ne_zero
  ---- Case 4: `n = 2k + 1` with `k > 0`
  · replace h := jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr h)
    simp only [Nat.cast_pow, jacobiSym_pow_left_odd'_eq_self] at h
    set D := 2 ^ (2 * (k + 1) + 1) + N
    have hN4 {n : ℕ} (h : n % 2 = 1) : jacobiSym n D = jacobiSym D n := by
      refine jacobiSym.quadratic_reciprocity_one_mod_four'
        (Nat.odd_iff.mpr h) (?_ : (_ + _) % 4 = 1)
      rw [add_comm, pow_succ, Nat.mul_succ 2, Nat.pow_add, mul_right_comm,
        Nat.add_mul_mod_self_right, ← Nat.mod_mod_of_dvd N ⟨15, rfl⟩, hN]
    have hN5 : jacobiSym D 5 = -1 := by
      have hN5 : (D : ℤ) % 5 = 2 ^ (2 * (k + 1) + 1) % 5 := by
        rw [← Int.ModEq, Int.modEq_iff_dvd, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
          sub_add_cancel_left, dvd_neg, Int.dvd_iff_emod_eq_zero, ← Nat.cast_ofNat,
          ← Int.natCast_mod, Nat.cast_eq_zero, ← Nat.mod_mod_of_dvd N ⟨12, rfl⟩, hN]
      rw [jacobiSym.mod_left' hN5, jacobiSym_pow_left_odd'_eq_self]; rfl
    have hN3 : jacobiSym D 3 = 1 := by
      have hN3 : (D : ℤ) % 3 = 1 % 3 := by
        have h0 : 2 ^ 2 % 3 = 1 := by rfl
        replace h0 : 2 ^ (2 * (k + 1) + 1) % 3 = 2 := by
          rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, h0, one_pow]; rfl
        rw [← Nat.cast_ofNat, ← Int.natCast_mod, ← Nat.cast_one, ← Int.natCast_mod,
          Nat.cast_inj, Nat.add_mod, h0, ← Nat.mod_mod_of_dvd N ⟨20, rfl⟩, hN]
      rw [jacobiSym.mod_left' hN3, jacobiSym.one_left]
    rw [hN4 (by rfl), hN4 (by rfl), hN5, hN3] at h
    exact absurd h (ne_of_beq_false rfl)

/-- Final solution -/
theorem final_solution (h : 5 ^ n ≡ 3 ^ n [MOD 2 ^ n + 65]) : n = 0 :=
  final_solution_general (Nat.add_mod_left 60 5) h
