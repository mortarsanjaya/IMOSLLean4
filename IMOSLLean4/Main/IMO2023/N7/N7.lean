/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.ModEq

/-!
# IMO 2023 N7

Find all possible values of $a + b + c + d$ across all $a, b, c, d ∈ ℕ^+$ satisfying
$$ \frac{ab}{a + b} + \frac{cd}{c + d} = \frac{(a + b)(c + d)}{a + b + c + d}. $$
-/

namespace IMOSL
namespace IMO2023N7

class nice (a b c d : ℕ) : Prop where
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  d_pos : 0 < d
  spec : ((a * b : ℕ) : ℚ) / (a + b : ℕ) + (c * d : ℕ) / (c + d : ℕ)
    = (a + b : ℕ) * (c + d : ℕ) / (a + b + c + d : ℕ)

theorem nice_of_special_form (hk : 0 < k) (hn : 0 < n) :
    nice (k * n ^ 2) (k * n) (k * n) k := by
  have hkn : 0 < k * n := mul_pos hk hn
  have hkn2 : 0 < k * n ^ 2 := mul_pos hk (pow_pos hn 2)
  refine ⟨hkn2, hkn, hkn, hk, ?_⟩
  replace hn : (n : ℚ) ≠ 0 := (Nat.cast_pos.mpr hn).ne.symm
  replace hkn : ((k * n.succ : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos hk n.succ_pos).ne.symm
  rw [sq, ← mul_assoc k, ← Nat.mul_succ, ← Nat.mul_succ, k.mul_right_comm n n.succ,
    mul_right_comm, Nat.cast_mul, Nat.cast_mul _ n, mul_div_mul_right _ _ hn, ← add_div,
    ← mul_assoc, ← Nat.cast_add, ← Nat.mul_succ, Nat.mul_assoc, Nat.cast_mul, add_assoc,
    mul_div_cancel_right₀ _ hkn, ← Nat.mul_succ, ← Nat.mul_succ, Nat.cast_mul (_ * _),
    mul_assoc, mul_div_mul_left _ _ hkn, Nat.cast_mul, Nat.cast_mul, ← mul_rotate',
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr n.succ_ne_zero), mul_comm]

theorem eq_nice_sum_of_not_Squarefree (hn : 0 < n) (h : ¬Squarefree n) :
    ∃ a b c d, nice a b c d ∧ a + b + c + d = n := by
  rw [Nat.squarefree_iff_prime_squarefree] at h
  simp only [not_forall, not_not] at h
  rcases h with ⟨p, hp, k, rfl⟩
  refine ⟨_, _, _, _, nice_of_special_form (Nat.pos_of_mul_pos_left hn) hp.pred_pos, ?_⟩
  rw [sq, ← mul_assoc, ← Nat.mul_succ, add_assoc, ← Nat.mul_succ, mul_right_comm,
    ← Nat.mul_succ, Nat.succ_pred_eq_of_pos hp.pos, mul_rotate]

theorem nice_sum_not_Squarefree (h : nice a b c d) : ¬Squarefree (a + b + c + d) := λ h0 ↦ by
  have hab : 0 < a + b := Nat.add_pos_left h.a_pos b
  have hcd : 0 < c + d := Nat.add_pos_left h.c_pos d
  replace h : a + b + (c + d) ∣ ((a + b) * (c + d)) ^ 2 := by
    replace hab : 0 < ((a + b : ℕ) : ℚ) := Nat.cast_pos.mpr hab
    replace hcd : 0 < ((c + d : ℕ) : ℚ) := Nat.cast_pos.mpr hcd
    have h1 := h.spec
    rw [div_add_div _ _ hab.ne.symm hcd.ne.symm, add_assoc, (a + b).cast_add,
      div_eq_div_iff (mul_pos hab hcd).ne.symm (add_pos hab hcd).ne.symm] at h1
    simp only [← Nat.cast_add, ← Nat.cast_mul] at h1
    rw [Nat.cast_inj, ← sq] at h1; exact Dvd.intro_left _ h1
  rw [Nat.add_assoc] at h0
  generalize a + b = k, c + d = m at h h0 hab hcd; clear a b c d
  ---- Now focus the problem on `k + m ∣ (km)^2`, where `k, m > 0` and `k + m` squarefree
  have h1 : k ^ 2 ≡ m ^ 2 [MOD k + m] := by
    rw [Nat.modEq_iff_dvd, Nat.cast_add, Nat.cast_pow, Nat.cast_pow, add_comm]
    exact ⟨m - k, sq_sub_sq _ _⟩
  replace h1 : k ^ 2 * k ^ 2 % (k + m) = k ^ 2 * m ^ 2 % (k + m) := h1.mul_left _
  rw [← pow_add, ← mul_pow, Nat.mod_eq_zero_of_dvd h] at h1
  replace h1 : k + m ∣ k :=
    (h0.dvd_pow_iff_dvd (Nat.succ_ne_zero 3)).mp (Nat.dvd_of_mod_eq_zero h1)
  exact (Nat.le_of_dvd hab h1).not_gt (Nat.lt_add_of_pos_right hcd)

/-- Final solution -/
theorem final_solution (hn : 0 < n) :
    (∃ a b c d, nice a b c d ∧ a + b + c + d = n) ↔ ¬Squarefree n :=
  ⟨λ ⟨_, _, _, _, h, h0⟩ ↦ h0 ▸ nice_sum_not_Squarefree h, eq_nice_sum_of_not_Squarefree hn⟩
