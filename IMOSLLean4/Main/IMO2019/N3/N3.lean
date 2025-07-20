/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.ModEq

/-!
# IMO 2019 N3

A set $S ⊆ ℤ$ is called *rootiful* if for any $a_0, a_1, … a_n ∈ S$, not all zero,
  and $x ∈ ℤ$ such that $a_0 + a_1 x + … + a_n x^n = 0$, we have $x ∈ S$.

Fix an integer $N$ with $|N| > 1$.
Find all rootiful sets containing $N^{a + 1} - N^{b + 1}$ for all $a, b ∈ ℕ$.
-/

namespace IMOSL
namespace IMO2019N3

open List

/-- Given `b k : ℤ` with `k ≠ 0`, there exists `m ≠ n` such that `b^m ≡ b^n (mod k)`. -/
theorem exists_ne_pow_eq (h : k ≠ 0) (b : ℤ) : ∃ m n : ℕ, m ≠ n ∧ k ∣ b ^ m - b ^ n :=
  have h0 : Set.MapsTo (λ x : ℕ ↦ b ^ x % k) Set.univ (Finset.Ico 0 |k|) :=
    λ x _ ↦ Finset.coe_Ico 0 |k| ▸ ⟨(b ^ x).emod_nonneg h, Int.emod_lt_abs _ h⟩
  (Set.infinite_univ.exists_ne_map_eq_of_mapsTo h0 (Set.toFinite _)).elim
    λ m ⟨_, n, _, h, h0⟩ ↦ ⟨m, n, h, Int.ModEq.dvd h0.symm⟩





/-! ### Start of the problem -/

def rootiful (S : Set ℤ) :=
  ∀ (x : ℤ) (P : List ℤ) (_ : ∀ a : ℤ, a ∈ P → a ∈ S) (_ : ∃ a : ℤ, a ∈ P ∧ a ≠ 0),
    P.foldr (· + x * ·) 0 = 0 → x ∈ S

theorem univ_rootiful : rootiful Set.univ := λ x _ _ _ _ ↦ Set.mem_univ x



section

variable {S : Set ℤ} (h : rootiful S)
include h

theorem rootiful_neg_one_mem (x : ℤ) (h0 : x ≠ 0) (h1 : x ∈ S) : (-1 : ℤ) ∈ S :=
  h (-1) (replicate 2 x)
    (λ _ h2 ↦ Set.mem_of_eq_of_mem (eq_of_mem_replicate h2) h1)
    ⟨x, mem_replicate.mpr ⟨Nat.succ_ne_zero 1, rfl⟩, h0⟩
    (by change x + -1 * (x + 0) = 0; rw [add_zero, neg_one_mul, add_neg_cancel])

theorem rootiful_one_mem_of_nat (n : ℕ) (h0 : n ≠ 0) (h1 : (n : ℤ) ∈ S) : (1 : ℤ) ∈ S :=
  let h0 : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr h0
  h 1 (n :: replicate n (-1))
    (forall_mem_cons.mpr
      ⟨h1, λ x h2 ↦ (mem_replicate.mp h2).2 ▸ rootiful_neg_one_mem h n h0 h1⟩)
    ⟨n, mem_cons_self, h0⟩
    (by simp only [one_mul]; rw [← sum_eq_foldr, sum_cons,
      sum_replicate, nsmul_eq_mul, mul_neg_one, add_neg_cancel])

theorem rootiful_one_mem_of_pos (n : ℤ) (h0 : 0 < n) (h1 : n ∈ S) : (1 : ℤ) ∈ S :=
  rootiful_one_mem_of_nat h n.natAbs (Int.natAbs_ne_zero.mpr h0.ne.symm)
    (Int.eq_natAbs_of_nonneg h0.le ▸ h1)

theorem rootiful_neg_mem_of_one_mem (h0 : (1 : ℤ) ∈ S) (x : ℤ) (h1 : x ∈ S) : -x ∈ S :=
  h (-x) [x, 1]
    (λ a h2 ↦ by
      rw [mem_cons, mem_singleton] at h2
      rcases h2 with rfl | rfl; exacts [h1, h0])
    ⟨1, mem_cons_of_mem _ (mem_singleton_self 1), Int.one_ne_zero⟩
    (by show x + -x * (1 + -x * 0) = 0; rw [mul_zero, add_zero, mul_one, add_neg_cancel])

theorem rootiful_neg_mem_of_pos {x : ℤ} (h0 : 0 < x) (h1 : x ∈ S) : -x ∈ S :=
  rootiful_neg_mem_of_one_mem h (rootiful_one_mem_of_pos h x h0 h1) x h1

theorem rootiful_induction_of_nat_dvd_nat (h0 : 1 < n) (h1 : ∀ k : ℕ, k < n → (k : ℤ) ∈ S)
    (N : ℕ) (h2 : 0 < N) (h3 : n ∣ N) (h4 : -(N : ℤ) ∈ S) : (n : ℤ) ∈ S :=
  h3.elim λ K h3 ↦ h n (-(N : ℕ) :: (n.digits K).map Nat.cast)
    (forall_mem_cons.mpr ⟨h4, λ x h5 ↦ by
      rw [mem_map] at h5; rcases h5 with ⟨d, h5, rfl⟩
      exact h1 d (Nat.digits_lt_base h0 h5)⟩)
    ⟨-N, mem_cons_self, by rw [Int.neg_ne_zero, Nat.cast_ne_zero]; exact h2.ne.symm⟩
    (by rw [List.foldr, foldr_map, ← Nat.ofDigits_eq_foldr, ← Nat.coe_int_ofDigits,
      Nat.ofDigits_digits, h3, Nat.cast_mul, neg_add_cancel])

theorem rootiful_induction_of_nat_dvd_int (h0 : 1 < n) (h1 : ∀ k : ℕ, k < n → (k : ℤ) ∈ S)
    (N : ℤ) (h2 : N ≠ 0) (h3 : (n : ℤ) ∣ N) (h4 : N ∈ S) : (n : ℤ) ∈ S :=
  have h2 := Int.natAbs_pos.mpr h2
  rootiful_induction_of_nat_dvd_nat h h0 h1 N.natAbs h2 (Int.natCast_dvd.mp h3)
    (N.natAbs_eq.symm.elim
      (λ h5 ↦ h5 ▸ h4) (λ h5 ↦ rootiful_neg_mem_of_pos h (Nat.cast_pos.mpr h2) (h5 ▸ h4)))

theorem rootiful_nat_subset (h0 : (0 : ℤ) ∈ S) (h1 : (1 : ℤ) ∈ S)
    (h2 : ∀ k : ℕ, 0 < k → ∃ N : ℤ, N ≠ 0 ∧ (k : ℤ) ∣ N ∧ N ∈ S) (k : ℕ) : (k : ℤ) ∈ S := by
  induction' k using Nat.strong_induction_on with k h3
  match k with
  | 0 => exact h0
  | 1 => exact h1
  | k + 2 =>
      rcases h2 (k + 2) k.succ.succ_pos with ⟨N, h4, h5, h6⟩
      exact rootiful_induction_of_nat_dvd_int h (Nat.succ_lt_succ k.succ_pos) h3 N h4 h5 h6

theorem rootiful_eq_univ (h0 : (0 : ℤ) ∈ S) (h1 : (1 : ℤ) ∈ S)
    (h2 : ∀ k : ℕ, 0 < k → ∃ N : ℤ, N ≠ 0 ∧ (k : ℤ) ∣ N ∧ N ∈ S) : S = Set.univ := by
  refine Set.eq_univ_of_forall λ k ↦ ?_
  have h3 := rootiful_nat_subset h h0 h1 h2 k.natAbs
  rcases le_or_gt 0 k with h4 | h4
  · rwa [Int.natAbs_of_nonneg h4] at h3
  · apply rootiful_neg_mem_of_pos h (Nat.cast_pos.mpr (Int.natAbs_pos.mpr h4.ne)) at h3
    rwa [Int.ofNat_natAbs_of_nonpos h4.le, neg_neg] at h3

end



/-- Final solution -/
theorem final_solution {N : ℤ} (h : 1 < |N|) {S : Set ℤ} :
    (rootiful S ∧ ∀ a b : ℕ, N ^ (a + 1) - N ^ (b + 1) ∈ S) ↔ S = Set.univ := by
  refine ⟨λ h0 ↦ ?_, λ h0 ↦ h0 ▸ ⟨univ_rootiful, λ _ _ ↦ Set.mem_univ _⟩⟩
  rcases h0 with ⟨h0, h1⟩; apply rootiful_eq_univ h0 (sub_self (N ^ 1) ▸ h1 0 0)
  ---- `1 ∈ S`
  · refine rootiful_one_mem_of_pos h0 (N ^ 2 - N ^ 1) ?_ (h1 1 0)
    rw [sub_pos, pow_one, ← sq_abs, sq]
    exact (le_abs_self _).trans_lt (lt_mul_self h)
  ---- Induction step
  · intro k h2; rcases exists_ne_pow_eq (Nat.cast_pos.mpr h2).ne.symm N with ⟨m, n, h3, h4⟩
    specialize h1 m n; rw [pow_succ, pow_succ, ← sub_mul] at h1
    refine ⟨_, mul_ne_zero ?_ (abs_pos.mp (Int.one_pos.trans h)), h4.mul_right N, h1⟩
    intro h5; refine h3 (Int.pow_right_injective ?_ (sub_eq_zero.mp h5))
    exact (Int.natAbs_lt_natAbs_of_nonneg_of_lt Int.one_nonneg h).trans_eq N.natAbs_abs
