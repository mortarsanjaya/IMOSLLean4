/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.ZMod.Defs

/-!
# IMO 2009 N1 (P1)

Let $n$ be a positive integer.
Let $a_1, a_2, …, a_k$ be distinct integers in $\{1, 2, …, n\}$, with $k > 1$.
Prove that there exists $i ≤ k$ such that $n$ does not divide $a_i (a_{i + 1} - 1)$.
Here, we denote $a_{k + 1} = a_1$.
-/

namespace IMOSL
namespace IMO2009N1

theorem easy_lemma {a b c n : ℤ} (h : n ∣ a * (b - 1)) (h0 : n ∣ b * (c - 1)) :
    n ∣ a * (c - 1) := by
  rw [Int.dvd_iff_emod_eq_zero, mul_sub_one,
    ← Int.emod_eq_emod_iff_emod_sub_eq_zero] at h h0 ⊢
  rw [Int.mul_emod, ← h, ← Int.mul_emod, mul_assoc, Int.mul_emod, h0, ← Int.mul_emod]

open Fin.NatCast in
theorem main_lemma {a : Fin (Nat.succ k) → ℤ} (ha : ∀ i, n ∣ a i * (a (i + 1) - 1)) :
    ∀ i j, n ∣ a i - a j := by
  have h (i) : ∀ m : ℕ, n ∣ a i * (a (i + (m.succ : Fin k.succ)) - 1) :=
    Nat.rec (ha i) λ m hm ↦ by rw [Nat.cast_succ, ← add_assoc]; exact easy_lemma hm (ha _)
  replace h (i j) : n ∣ a i * a j - a i := by
    have h0 := h i (j - i - 1 : Fin k.succ)
    rwa [Nat.cast_succ, Fin.cast_val_eq_self,
      sub_add_cancel, add_sub_cancel, mul_sub_one] at h0
  intro i j; rw [← sub_sub_sub_cancel_left _ _ (a i * a j)]
  exact Int.dvd_sub (mul_comm (a i) (a j) ▸ h j i) (h i j)

/-- Final solution -/
theorem final_solution (hk : 1 < Nat.succ k) {a : Fin (Nat.succ k) → ℤ}
    (ha : a.Injective) {n : ℕ} (ha0 : ∀ i, 0 < a i ∧ a i ≤ n) :
    ¬∀ i, (n : ℤ) ∣ a i * (a (i + 1) - 1) := λ ha1 ↦ by
  replace ha0 (i) : (a i - 1) % n = a i - 1 :=
    let ⟨h, h0⟩ := (ha0 i).imp Int.le_sub_one_of_lt Int.sub_one_lt_of_le
    Int.emod_eq_of_lt h h0
  replace ha1 : (n : ℤ) ∣ a 0 - a 1 := main_lemma ha1 0 1
  rw [← sub_sub_sub_cancel_right _ _ 1, Int.dvd_iff_emod_eq_zero,
    ← Int.emod_eq_emod_iff_emod_sub_eq_zero, ha0, ha0, sub_left_inj] at ha1
  exact hk.ne.symm (Fin.one_eq_zero_iff.mp (ha ha1).symm)
