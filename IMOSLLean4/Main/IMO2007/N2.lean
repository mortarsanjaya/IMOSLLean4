/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int

/-!
# IMO 2007 N2

Fix some $b, n ∈ ℕ$ with $b > 0$.
Suppose that for each $k ∈ ℕ⁺$, there exists an integer $a$ such that $k ∣ b - a^n$.
Prove that $b = A^n$ for some non-negative integer $A$.

### Solution

We use the following very short solution.
Take $k = b^2$, and write $b - a^n = b^2 d$ for some integers $a$ and $d$.
Then rearranging gives $a^n = b(1 - bd)$.
Since $b > 0$ and $\gcd(b, 1 - bd) = 1$, so $b$ must be an $n$th power.
-/

namespace IMOSL
namespace IMO2007N2

/-- If `b ∈ ℕ` and `b^2 ∣ b - a^n` for some `a ∈ ℤ`, then `b = A^n` for some `A ∈ ℕ`. -/
theorem eq_pow_of_sq_dvd_self_sub_pow {b n : ℕ} (h : ∃ a, (b : ℤ) ^ 2 ∣ b - a ^ n) :
    ∃ A, b = A ^ n := by
  ---- Write `b - a^n = b^2 d` for some `d ∈ ℤ`.
  rcases h with ⟨a, d, h⟩
  ---- Rewrite the equality as `a^n = b(1 - bd)`.
  replace h : a ^ n = b * (1 - b * d) := by
    rw [mul_one_sub, ← Int.mul_assoc, ← sq, ← h, sub_sub_cancel]
  ---- Since `gcd(b, 1 - bd) = 1`, this means `b = ±c^n` for some `c ∈ ℤ`.
  obtain ⟨c, hc⟩ : ∃ c : ℤ, Associated (c ^ n) b := by
    refine exists_associated_pow_of_mul_eq_pow ?_ h.symm
    -- It remains to show that `gcd(b, 1 - bd) = 1`.
    have h0 : (b : ℤ) ∣ (1 - b * d) - 1 := ⟨-d, by rw [sub_sub_cancel_left, mul_neg]⟩
    rw [gcd_eq_of_dvd_sub_right h0, gcd_one_right]
    exact isUnit_one
  ---- Then `|c|^n = b`, since `b > 0`.
  rw [Int.associated_iff_natAbs, Int.natAbs_pow, Int.natAbs_natCast] at hc
  exact ⟨c.natAbs, hc.symm⟩

/-- Final solution -/
theorem final_solution {b n : ℕ} (hb : 0 < b) (h : ∀ k > 0, ∃ c : ℤ, k ∣ b - c ^ n) :
    ∃ A, b = A ^ n :=
  eq_pow_of_sq_dvd_self_sub_pow (h (b ^ 2) (sq_pos_of_pos (Int.natCast_pos.mpr hb)))
