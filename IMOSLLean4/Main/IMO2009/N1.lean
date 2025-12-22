/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Int.ModEq

/-!
# IMO 2009 N1 (P1)

Let $n$ be a positive integer.
Let $a_1, a_2, …, a_k$ be distinct integers in $\{1, 2, …, n\}$, with $k > 1$.
Prove that there exists $i ≤ k$ such that $n$ does not divide $a_i (a_{i + 1} - 1)$.
Here, we denote $a_{k + 1} = a_1$.

### Solution

We follow Solution 2 of the
  [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
-/

namespace IMOSL
namespace IMO2009N1

open Fin.NatCast in
/-- If `a_1, a_2, …, a_k` satisfies `a_i a_{i + 1} ≡ a_i (mod n)` for all `i ≤ k`,
  where we denote `a_{k + 1} = a_1`, then all the `a_i`'s are congruent mod `n`. -/
theorem main_lemma {a : Fin (Nat.succ k) → ℤ} (ha : ∀ i, a i * a (i + 1) ≡ a i [ZMOD n]) :
    ∀ i j, a i ≡ a j [ZMOD n] := by
  ---- By inducting, we get `a_i a_{i + m + 1} ≡ a_i (mod n)` for all `i` and `m ∈ ℕ`.
  have h (i : Fin k.succ) (m : ℕ) : a i * (a (i + ((m + 1) : ℕ))) ≡ a i [ZMOD n] := by
    induction m with | zero => exact ha i | succ m m_ih => ?_
    calc a i * a (i + (m + 1 + 1 : ℕ))
      _ = a i * a (i + (m + 1 : ℕ) + 1) := by rw [Nat.cast_succ, add_assoc]
      _ ≡ a i * a (i + (m + 1 : ℕ)) * a (i + (m + 1 : ℕ) + 1) [ZMOD n] :=
        m_ih.symm.mul_right _
      _ = a i * (a (i + (m + 1 : ℕ)) * a (i + (m + 1 : ℕ) + 1)) := Int.mul_assoc _ _ _
      _ ≡ a i * a (i + (m + 1 : ℕ)) [ZMOD n] := (ha _).mul_left _
      _ ≡ a i [ZMOD n] := m_ih
  ---- Then `a_i a_j ≡ a_i (mod n)` for all `i` and `j`.
  replace h (i j : Fin k.succ) : a i * a j ≡ a i [ZMOD n] := by
    have h0 := h i (j - i - 1 : Fin k.succ)
    rwa [Nat.cast_succ, Fin.cast_val_eq_self, sub_add_cancel, add_sub_cancel] at h0
  ---- The rest is easy.
  intro i j; calc a i
    _ ≡ a i * a j [ZMOD n] := (h i j).symm
    _ = a j * a i := by rw [mul_comm]
    _ ≡ a j [ZMOD n] := h j i

/-- Final solution -/
theorem final_solution (hk : 1 < Nat.succ k) {a : Fin (Nat.succ k) → ℤ}
    (ha : a.Injective) {n : ℕ} (ha0 : ∀ i, 0 < a i ∧ a i ≤ n) :
    ¬∀ i, (n : ℤ) ∣ a i * (a (i + 1) - 1) := by
  ---- If not, then `a_1 - 1 ≡ a_0 - 1 (mod n)`.
  intro ha1
  replace ha1 (i) : a i * a (i + 1) ≡ a i [ZMOD n] := by
    specialize ha1 i
    rwa [Int.mul_sub, Int.mul_one, ← Int.modEq_iff_dvd, Int.modEq_comm] at ha1
  replace ha1 : (a 1 - 1) % n = (a 0 - 1) % n := (main_lemma ha1 1 0).sub_right _
  ---- But then `a_1 = a_0`; contradiction.
  replace ha0 (i) : (a i - 1) % n = a i - 1 :=
    Int.emod_eq_of_lt (Int.le_sub_one_of_lt (ha0 i).1) (Int.sub_one_lt_of_le (ha0 i).2)
  replace ha1 : a 1 = a 0 := by rwa [ha0, ha0, Int.sub_left_inj] at ha1
  exact absurd (ha ha1) (λ h ↦ hk.ne.symm (Fin.one_eq_zero_iff.mp h))
