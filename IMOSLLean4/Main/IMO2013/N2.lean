/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Parity

/-!
# IMO 2013 N2 (P1)

Prove that, for any $k, n ∈ ℕ⁺$, there exist positive integers $m_1, m_2, …, m_k$ such that
$$ 1 + \frac{2^k - 1}{n} = \prod_{i = 1}^k \left(1 + \frac{1}{m_i}\right). $$

### Solution

We follow Solution 1 of the official solution with a slight modification.
See [here](https://www.imo-official.org/problems/IMO2013SL.pdf).
The induction step is proved with $2^k - 1$ generalized to any positive integer.
For generality (and more importantly, reducing import),
  we work over fields of characteristic zero.
-/

namespace IMOSL
namespace IMO2013N2

open Multiset

/-- We say that a pair `(k, c)` of non-negative integers *good* if for any `n > 0`,
  there exists positive integers `m_1, …, m_k` such that `1 + c/n` is equal to
  `(1 + 1/m_1) … (1 + 1/m_k)`; our goal is to prove that `(k, 2^k - 1)` is good. -/
def good (F) [Field F] (k c : ℕ) :=
  ∀ n > 0, ∃ S : Multiset ℕ, S.card = k ∧ (∀ m ∈ S, 0 < m) ∧
    ((n + c : ℕ) : F) / n = (S.map λ m ↦ ((m + 1 : ℕ) : F) / m).prod

/-- If `(k, c)` is good, then `(k + 1, 2c + 1)` is good. -/
theorem good_two_mul_add_one [Field F] [CharZero F] (h : good F k c) :
    good F (k + 1) (2 * c + 1) := by
  ---- Divide into two cases: `n` is even and `n` is odd.
  intro n h0
  obtain ⟨t, rfl | rfl⟩ : ∃ t, n = 2 * t ∨ n = 2 * t + 1 := n.even_or_odd'
  ---- Case 1: `n` is even, say `n = 2t`.
  · -- First represent `1 + c/t` as `(1 + 1/m_1) … (1 + 1/m_k)`.
    obtain ⟨T, rfl, h1, h2⟩ : ∃ T : Multiset ℕ, T.card = k ∧ (∀ m ∈ T, 0 < m) ∧
        ((t + c : ℕ) : F) / t = (T.map λ m ↦ ((m + 1 : ℕ) : F) / m).prod :=
      h t (Nat.pos_of_mul_pos_left h0)
    replace h0 : 0 < t + c := t.add_pos_left (Nat.pos_of_mul_pos_left h0) c
    -- Now claim that `m_{k + 1} = 2(t + c)` works.
    refine ⟨(2 * (t + c)) ::ₘ T, T.card_cons _,
      forall_mem_cons.mpr ⟨Nat.mul_pos Nat.two_pos h0, h1⟩, ?_⟩
    -- Claim follows from `1 + (2c + 1)/(2t) = (1 + c/t)(1 + 1/(2(t + c)))`.
    calc ((2 * t + (2 * c + 1) : ℕ) : F) / (2 * t : ℕ)
    _ = (2 * (t + c) + 1 : ℕ) / (2 * t : ℕ) := by
      rw [Nat.mul_add, Nat.add_assoc]
    _ = (2 * (t + c) + 1 : ℕ) / (2 * (t + c) : ℕ) * ((t + c : ℕ) / t) := by
      rw [Nat.cast_mul, Nat.cast_mul, ← div_div, ← div_div,
        div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr h0.ne.symm)]
    _ = ((2 * (t + c) ::ₘ T).map λ (m : ℕ) ↦ (m.succ : F) / m).prod := by
      rw [map_cons, prod_cons, ← h2]
  ---- Case 2: `n` is odd, say `n = 2t + 1`.
  · -- First represent `1 + c/(t + 1)` as `(1 + 1/m_1) … (1 + 1/m_k)`.
    obtain ⟨T, rfl, h1, h2⟩ : ∃ T : Multiset ℕ, T.card = k ∧ (∀ m ∈ T, 0 < m) ∧
        ((t + 1 + c : ℕ) : F) / (t + 1 : ℕ) = (T.map λ m ↦ ((m + 1 : ℕ) : F) / m).prod :=
      h (t + 1) t.succ_pos
    -- Now claim that `m_{k + 1} = 2t + 1` works.
    refine ⟨(2 * t + 1) ::ₘ T, T.card_cons _, forall_mem_cons.mpr ⟨h0, h1⟩, ?_⟩
    -- Claim follows from `1 + (2c + 1)/(2t + 1) = (1 + 1/(2t + 1))(1 + c/(t + 1))`.
    calc ((2 * t + 1 + (2 * c + 1) : ℕ) : F) / (2 * t + 1 : ℕ)
    _ = (2 * (t + c + 1) : ℕ) / (2 * t + 1 : ℕ) := by
      rw [Nat.add_add_add_comm, Nat.mul_succ, Nat.mul_add]
    _ = (2 * (t + 1) : ℕ) / (2 * t + 1 : ℕ) * ((t + c + 1 : ℕ) / (t + 1 : ℕ)) := by
      rw [Nat.cast_mul, Nat.cast_mul, mul_div_assoc, mul_div_assoc, mul_assoc,
        div_mul_div_cancel₀' (Nat.cast_ne_zero.mpr t.succ_ne_zero)]
    _ = (((2 * t + 1) ::ₘ T).map λ (m : ℕ) ↦ (m.succ : F) / m).prod := by
      rw [map_cons, prod_cons, ← h2, Nat.add_right_comm]; rfl

/-- Final solution -/
theorem final_solution (F) [Field F] [CharZero F] (k) : good F k (2 ^ k - 1) := by
  induction k with
  | zero =>
      intro n hn; exact ⟨0, rfl, λ m h ↦ absurd h (notMem_zero m),
        div_self (Nat.cast_ne_zero.mpr hn.ne.symm)⟩
  | succ k hk =>
      suffices 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 from this ▸ good_two_mul_add_one hk
      have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [Nat.two_mul, Nat.add_assoc, Nat.sub_add_cancel h,
        Nat.pow_succ, Nat.mul_two, Nat.sub_add_comm h]
