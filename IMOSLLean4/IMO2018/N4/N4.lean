/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.NatSequence.AntitoneConst
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# IMO 2018 N4 (P5)

Let $(a_n)_{n ≥ 1}$ be a sequence of positive integers such that for $n$ large enough,
$$ \frac{a_1}{a_2} + \frac{a_2}{a_3} + … + \frac{a_{n - 1}}{a_n} + \frac{a_n}{a_1} ∈ ℤ. $$
Prove that $(a_n)_{n ≥ 1}$ is eventually constant.
-/

namespace IMOSL
namespace IMO2018N4

lemma lemma1 {a c : ℕ} (h : a * a.gcd c ∣ c ^ 2) : a ∣ c := by
  obtain rfl | ha : a = 0 ∨ 0 < a := a.eq_zero_or_pos
  · rw [Nat.zero_mul, Nat.zero_dvd, sq, Nat.mul_eq_zero, or_self] at h
    exact Nat.zero_dvd.mpr h
  · replace h : a * a.gcd c ∣ c * a.gcd c := by
      rw [c.mul_comm, ← Nat.gcd_mul_right, ← sq]
      exact Nat.dvd_gcd (Nat.mul_dvd_mul_left a (a.gcd_dvd_right c)) h
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.gcd_pos_of_pos_left c ha) h

lemma lemma2 {a b c : ℕ} (h : a.gcd b * c ∣ a * b + c ^ 2) : a.gcd b ∣ a.gcd c := by
  replace h : a.gcd b * (a.gcd b).gcd c ∣ a * b + c ^ 2 :=
    Nat.dvd_trans (Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_right _ _)) h
  replace h : a.gcd b * (a.gcd b).gcd c ∣ c ^ 2 := by
    refine (Nat.dvd_add_right (Nat.mul_dvd_mul (a.gcd_dvd_left b) ?_)).mp h
    exact (Nat.gcd_dvd_left _ _).trans (a.gcd_dvd_right b)
  exact Nat.dvd_gcd (a.gcd_dvd_left b) (lemma1 h)

lemma lemma3 {a b c : ℕ} (h : a.gcd b * c ∣ a * b + c ^ 2) : c * a.gcd b ∣ b * a.gcd c := by
  replace h : a.gcd b * c ∣ a * b := by
    refine (Nat.dvd_add_left (sq c ▸ ?_)).mp h
    exact Nat.mul_dvd_mul_right ((lemma2 h).trans (a.gcd_dvd_right c)) c
  rw [c.mul_comm, ← Nat.gcd_mul_left, b.mul_comm]
  exact Nat.dvd_gcd h (Nat.mul_dvd_mul_right (a.gcd_dvd_right b) c)

/-- Final solution -/
theorem final_solution {a : ℕ → ℕ} (ha : ∀ n, 0 < a n)
    (ha0 : ∃ K, ∀ n ≥ K, ∃ z : ℤ, (z : ℚ) =
      (∑ i ∈ Finset.range n, (a i : ℚ) / a (i + 1)) + a n / a 0) :
    ∃ C N, ∀ n, a (n + N) = C := by
  ---- First manipulate to `gcd(a_0, a_n) a_{n + 1} ∣ a_0 a_n + a_{n + 1}^2` for all `n` big
  replace ha0 : ∃ K, ∀ n ≥ K, (a 0).gcd (a n) * a (n + 1) ∣ a 0 * a n + a (n + 1) ^ 2 := by
    rcases ha0 with ⟨K, hK⟩
    refine ⟨K, λ n hn ↦ ?_⟩
    obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ℚ) = a n / a (n + 1) + (a (n + 1) - a n) / a 0 := by
      obtain ⟨z₁, h₁⟩ := hK n hn
      obtain ⟨z₂, h₂⟩ := hK (n + 1) (Nat.le_succ_of_le hn)
      refine ⟨z₂ - z₁, ?_⟩
      rw [Rat.intCast_sub, h₂, h₁, Finset.sum_range_succ, add_assoc,
        add_sub_add_left_eq_sub, add_sub_assoc, sub_div]
    replace ha (n) : (a n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ha n).ne.symm
    replace hz : z * (a (n + 1) * a 0) =
        (a n * a 0 + a (n + 1) ^ 2 : ℕ) - a (n + 1) * a n := by
      rw [← Rat.intCast_inj, sq, Int.cast_sub, Nat.cast_add, Int.cast_add]
      simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
      rwa [div_add_div _ _ (ha _) (ha _), mul_sub, ← add_sub_assoc,
        eq_div_iff (mul_ne_zero (ha _) (ha _))] at hz
    replace hz : a (n + 1) * (z * a 0 + a n) = (a n * a 0 + a (n + 1) ^ 2 : ℕ) := by
      rw [← add_eq_of_eq_sub hz, mul_left_comm, mul_add]
    rw [Nat.mul_comm, ← Int.natCast_dvd_natCast, (a 0).mul_comm, ← hz, Nat.cast_mul]
    refine Int.mul_dvd_mul_left _ (Int.dvd_add (dvd_mul_of_dvd_right ?_ _) ?_)
    · rw [Int.natCast_dvd_natCast]; exact Nat.gcd_dvd_left _ _
    · rw [Int.natCast_dvd_natCast]; exact Nat.gcd_dvd_right _ _
  ---- The sequence `a_0/gcd(a_0, a_n)` and `a_n/gcd(a_0, a_n)` are eventually constant
  rcases ha0 with ⟨K, hK⟩
  replace hK (n) :
      (a 0).gcd (a (n + K)) * a (n + 1 + K) ∣ a 0 * a (n + K) + a (n + 1 + K) ^ 2 :=
    n.add_right_comm K 1 ▸ hK _ (K.le_add_left n)
  have hK0 (n) : 0 < (a 0).gcd (a n) := Nat.gcd_pos_of_pos_left _ (ha 0)
  obtain ⟨M, C, h⟩ : ∃ C M, ∀ n, a 0 / (a 0).gcd (a (n + M + K)) = C := by
    let b (n) : ℕ := a 0 / (a 0).gcd (a (n + K))
    refine Extra.NatSeq_antitone_imp_const (a := b) (antitone_nat_of_succ_le λ n ↦ ?_)
    exact Nat.div_le_div_left (Nat.le_of_dvd (hK0 _) (lemma2 (hK n))) (hK0 _)
  obtain ⟨N, D, h0⟩ : ∃ D N, ∀ n, a (n + N + K) / (a 0).gcd (a (n + N + K)) = D := by
    let b (n) : ℕ := a (n + K) / (a 0).gcd (a (n + K))
    refine Extra.NatSeq_antitone_imp_const (a := b) (antitone_nat_of_succ_le λ n ↦ ?_)
    exact Nat.div_le_div_of_mul_le_mul (hK0 _).ne.symm (Nat.gcd_dvd_right _ _)
      (Nat.le_of_dvd (Nat.mul_pos (ha _) (hK0 _)) (lemma3 (hK n)))
  ---- Now finish
  refine ⟨a 0 / M * N, C + D + K, λ n ↦ ?_⟩
  replace h : a 0 = (a 0).gcd (a (n + D + C + K)) * M :=
    Nat.eq_mul_of_div_eq_right (Nat.gcd_dvd_left _ _) (h _)
  have hM : 0 < M := Nat.pos_of_dvd_of_pos (Dvd.intro_left _ h.symm) (ha 0)
  rw [h, Nat.mul_div_cancel _ hM, n.add_right_comm,
    ← h0 (n + C), ← n.add_assoc, ← n.add_assoc]
  exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
