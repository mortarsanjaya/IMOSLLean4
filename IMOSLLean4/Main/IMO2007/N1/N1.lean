/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int.Defs

/-!
# IMO 2007 N1

Find all pairs $(k, n) ∈ ℕ^2$ such that $7^k - 3^n ∣ k^4 + n^2$.
-/

namespace IMOSL
namespace IMO2007N1

/-! ### Extra lemmas -/

lemma sq_mod_four_of_odd (hm : m % 2 = 1) : m ^ 2 % 4 = 1 := by
  rcases Nat.odd_mod_four_iff.mp hm with hm | hm
  all_goals rw [Nat.pow_mod, hm]

lemma two_dvd_seven_pow_sub_three_pow (k n) : (2 : ℤ) ∣ 7 ^ k - 3 ^ n := by
  show ((2 : ℕ) : ℤ) ∣ (7 : ℕ) ^ k - (3 : ℕ) ^ n
  rw [← Int.natCast_pow, ← Int.natCast_pow, ← Nat.modEq_iff_dvd,
    Nat.ModEq, Nat.pow_mod, Nat.one_pow, Nat.pow_mod, Nat.one_pow]

lemma succ_pow_four_lt_seven_mul_pow_four (ha : 2 ≤ a) : (a + 1) ^ 4 < 7 * a ^ 4 := by
  calc (a + 1) ^ 3 * (a + 1)
    _ < (a + 1) ^ 3 * (2 * a) := by
      refine Nat.mul_lt_mul_of_pos_left ?_ (Nat.pow_pos a.succ_pos)
      rwa [Nat.two_mul, Nat.add_lt_add_iff_left]
    _ = 2 * (a + 1) ^ 3 * a := by rw [Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ 7 * a ^ 3 * a := Nat.mul_le_mul_right a ?_
    _ = 7 * a ^ 4 := by rw [Nat.mul_assoc, ← Nat.pow_succ]
  calc 2 * (a + 1) ^ 3
    _ = 2 * (((a + 2) * a + 1) * (a + 1)) := by
      rw [Nat.pow_succ, add_sq, Nat.mul_one, Nat.one_pow, sq, ← Nat.add_mul]
    _ = 2 * ((a + 2) * a * (a + 1) + (a + 1)) := by rw [Nat.succ_mul _ (a + 1)]
    _ ≤ 2 * ((a + 2) * a * (a + 1) + (a + 2)) := Nat.le_add_right _ 2
    _ = 2 * (a + 2) * (a * (a + 1) + 1) := by
      rw [Nat.mul_assoc, ← Nat.mul_succ, Nat.mul_assoc]
    _ ≤ 2 * (a + a) * (a * (a + 1) + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (Nat.add_le_add_left ha a))
    _ = a * (4 * (a * (a + 1) + 1)) := by
      rw [← Nat.two_mul, ← Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ a * (7 * (a * a)) := Nat.mul_le_mul_left _ ?_
    _ = 7 * a ^ 3 := by rw [Nat.mul_left_comm, ← sq, ← Nat.pow_succ']
  calc 4 * (a * (a + 1)) + 4
    _ = 4 * (a * a) + 2 * 2 * a + 2 * 2 := by rw [a.mul_succ, Nat.mul_add]
    _ ≤ 4 * (a * a) + 2 * a * a + a * a := by
      refine Nat.add_le_add (Nat.add_le_add_left ?_ _) (Nat.mul_self_le_mul_self ha)
      exact Nat.mul_le_mul_right a (Nat.mul_le_mul_left 2 ha)
    _ = 7 * (a * a) := by rw [Nat.mul_assoc, ← Nat.add_mul, ← Nat.succ_mul]

lemma succ_sq_lt_three_mul_sq (hb : 2 ≤ b) : (b + 1) ^ 2 < 3 * b ^ 2 := calc
  _ = b ^ 2 + 2 * b + 1 := by rw [add_sq, Nat.mul_one, Nat.one_pow]
  _ < b ^ 2 + 2 * b + 2 := Nat.lt_succ_self _
  _ ≤ b ^ 2 + b * b + b * b :=
    Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right b hb) _)
      (hb.trans b.le_mul_self)
  _ = 3 * b ^ 2 := by rw [← sq, ← Nat.two_mul, ← Nat.succ_mul]

lemma a_bound₀ (hn : 2 ≤ n) (hk : 8 * n ^ 4 + k < 7 ^ n) : ∀ a ≥ n, 8 * a ^ 4 + k < 7 ^ a :=
  Nat.le_induction hk λ a ha ha0 ↦ calc
    _ ≤ 8 * (7 * a ^ 4) + 7 * k :=
      Nat.add_le_add
        (Nat.mul_le_mul_left 8 (succ_pow_four_lt_seven_mul_pow_four (hn.trans ha)).le)
        (Nat.le_mul_of_pos_left k (Nat.succ_pos 6))
    _ = (8 * a ^ 4 + k) * 7 := by rw [Nat.mul_left_comm, ← Nat.mul_add, Nat.mul_comm]
    _ < _ := Nat.mul_lt_mul_of_pos_right ha0 (Nat.succ_pos 6)

lemma b_bound₀ (hn : 2 ≤ n) (hk : 2 * n ^ 2 + k < 3 ^ n) : ∀ b ≥ n, 2 * b ^ 2 + k < 3 ^ b :=
  Nat.le_induction hk λ b hb hb0 ↦ calc
    _ ≤ 2 * (3 * b ^ 2) + 3 * k :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 (succ_sq_lt_three_mul_sq (hn.trans hb)).le)
        (Nat.le_mul_of_pos_left k (Nat.succ_pos 2))
    _ = (2 * b ^ 2 + k) * 3 := by rw [Nat.mul_left_comm, ← Nat.mul_add, Nat.mul_comm]
    _ < _ := Nat.mul_lt_mul_of_pos_right hb0 (Nat.succ_pos 2)

lemma b_bound₁ : ∀ b, 2 * b ^ 2 < 3 ^ b
  | 0 => Nat.one_pos
  | 1 => Nat.lt_succ_self 2
  | n + 2 => b_bound₀ (k := 0) (Nat.le_refl 2) (Nat.lt_succ_self 8) _ (Nat.le_add_left 2 n)





/-! ### Start of the problem -/

def good (k n : ℕ) := (7 : ℤ) ^ k - 3 ^ n ∣ (k ^ 4 + n ^ 2 : ℕ)

lemma good_zero_zero : good 0 0 := ⟨0, rfl⟩

lemma good_two_four : good 2 4 := ⟨-1, by rfl⟩

lemma good_imp_even (h : good k n) : 2 ∣ k ∧ 2 ∣ n := by
  have h0 : Even (k + n) := by
    have h0 : 2 ∣ k ^ 4 + n ^ 2 :=
      Int.natCast_dvd_natCast.mp ((two_dvd_seven_pow_sub_three_pow k n).trans h)
    rwa [← even_iff_two_dvd, Nat.even_add, Nat.even_pow' (Nat.succ_ne_zero 3),
      Nat.even_pow' (Nat.succ_ne_zero 1), ← Nat.even_add] at h0
  suffices ¬k % 2 = 1 by
    rw [← Nat.odd_iff, Nat.not_odd_iff_even] at this
    exact ⟨even_iff_two_dvd.mp this, even_iff_two_dvd.mp ((Nat.even_add.mp h0).mp this)⟩
  intro h1; replace h0 : n % 2 = 1 := by
    rw [← Nat.odd_iff] at h1 ⊢; exact (Nat.even_add'.mp h0).mp h1
  replace h : 4 ∣ k ^ 4 + n ^ 2 := by
    refine Int.natCast_dvd_natCast.mp (dvd_trans ?_ h)
    show ((4 : ℕ) : ℤ) ∣ (7 : ℕ) ^ k - (3 : ℕ) ^ n
    rw [← Int.natCast_pow, ← Int.natCast_pow, ← Nat.modEq_iff_dvd, Nat.ModEq]
    have h2 : 3 ^ n % 4 = 3 := calc
      _ = 3 ^ (2 * (n / 2) + 1) % 4 := by rw [← h0, Nat.div_add_mod]
      _ = (3 ^ 2) ^ (n / 2) * 3 % 4 := by rw [Nat.pow_succ, Nat.pow_mul]
      _ = (3 ^ 2 % 4) ^ (n / 2) % 4 * 3 % 4 := by rw [← Nat.pow_mod, Nat.mod_mul_mod]
      _ = 1 ^ (n / 2) % 4 * 3 % 4 := rfl
      _ = 3 := by rw [Nat.one_pow]
    have h3 : 7 ^ k % 4 = 3 := calc
      _ = 7 ^ (2 * (k / 2) + 1) % 4 := by rw [← h1, Nat.div_add_mod]
      _ = (7 ^ 2) ^ (k / 2) * 7 % 4 := by rw [Nat.pow_succ, Nat.pow_mul]
      _ = (7 ^ 2 % 4) ^ (k / 2) % 4 * 7 % 4 := by rw [← Nat.pow_mod, Nat.mod_mul_mod]
      _ = 1 ^ (k / 2) % 4 * 7 % 4 := rfl
      _ = 3 := by rw [Nat.one_pow]
    exact h2.trans h3.symm
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, k.pow_mul 2 2,
    Nat.pow_mod, sq_mod_four_of_odd h1, sq_mod_four_of_odd h0] at h
  exact Nat.succ_ne_zero 1 h

lemma good_two_mul_imp₁ (h : good (2 * a) (2 * b)) :
    7 ^ a + 3 ^ b ∣ 8 * a ^ 4 + 2 * b ^ 2 := by
  rw [good, mul_pow, mul_pow, Nat.mul_comm, pow_mul, Nat.mul_comm, pow_mul, sq_sub_sq] at h
  replace h : ((7 : ℕ) ^ a + (3 : ℕ) ^ b : ℤ) * (2 : ℕ) ∣ _ :=
    (Int.mul_dvd_mul_left _ (two_dvd_seven_pow_sub_three_pow a b)).trans h
  rw [← Int.natCast_pow, ← Int.natCast_pow, ← Nat.cast_add, ← Nat.cast_mul, Int.ofNat_dvd,
    Nat.pow_succ', sq, Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.mul_comm] at h
  exact (mul_dvd_mul_iff_left (Nat.succ_ne_zero 1)).mp h

lemma good_two_mul_imp₂ (h : 7 ^ a + 3 ^ b ∣ 8 * a ^ 4 + 2 * b ^ 2) :
    (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b ≤ 2) := by
  ---- First resolve the case `a = 0`
  obtain rfl | ha : a = 0 ∨ 1 ≤ a := a.eq_zero_or_pos
  · left; refine ⟨rfl, ?_⟩
    replace h : 2 * b ^ 2 = 0 := by
      rw [Nat.add_comm, Nat.zero_pow (Nat.succ_pos 3), Nat.mul_zero, Nat.zero_add] at h
      exact Nat.eq_zero_of_dvd_of_lt h (Nat.lt_succ_of_lt (b_bound₁ b))
    rw [Nat.mul_eq_zero, Nat.pow_eq_zero] at h
    exact (h.resolve_left (Nat.succ_ne_zero 1)).1
  ---- For `a > 0`, we have `7^a + 3^b ≤ 8a^4 + 2b^2`
  right; have h0 : 7 ^ a + 3 ^ b ≤ 8 * a ^ 4 + 2 * b ^ 2 :=
    Nat.le_of_dvd (Nat.add_pos_left (Nat.mul_pos (Nat.succ_pos 7) (Nat.pow_pos ha)) _) h
  ---- Split into 4 cases: `a = 1`, `a = 2`, `a = 3`, and `a ≥ 4`
  rw [Nat.le_iff_lt_or_eq, ← Nat.succ_le, Nat.le_iff_lt_or_eq,
    ← Nat.succ_le, Nat.le_iff_lt_or_eq] at ha
  rcases ha with (((ha : 4 ≤ a) | (rfl : 3 = a)) | (rfl : 2 = a)) | (rfl : 1 = a)
  ---- Case 1: `a ≥ 4`
  · exfalso; refine h0.not_gt (Nat.add_lt_add ?_ (b_bound₁ b))
    exact a_bound₀ (n := 4) (k := 0) (by decide) (by decide) a ha
  ---- Case 2: `a = 3`
  · exfalso; obtain h1 | h1 : b < 6 ∨ 6 ≤ b := lt_or_ge b 6
    -- Subcase 1: `b < 6`
    · clear h0; revert h
      revert h1 b; decide
    -- Subcase 2: `b ≥ 6`
    · refine h0.not_gt (?_ : 343 + 305 + 2 * b ^ 2 < 343 + 3 ^ b)
      rw [Nat.add_assoc, Nat.add_lt_add_iff_left, Nat.add_comm]
      exact b_bound₀ (by decide) (by decide) b h1
  ---- Case 3: `a = 2`
  · exfalso; obtain h1 | h1 : b < 5 ∨ 5 ≤ b := lt_or_ge b 5
    -- Subcase 1: `b < 5`
    · clear h0; revert h
      revert h1 b; decide
    -- Subcase 2: `b ≥ 5`
    · refine h0.not_gt (?_ : 49 + 79 + 2 * b ^ 2 < 49 + 3 ^ b)
      rw [Nat.add_assoc, Nat.add_lt_add_iff_left, Nat.add_comm]
      exact b_bound₀ (by decide) (by decide) b h1
  ---- Case 4: `a = 1`
  · refine ⟨rfl, Nat.le_of_not_lt λ h1 ↦ h0.not_gt (?_ : 7 + 1 + 2 * b ^ 2 < 7 + 3 ^ b)⟩
    rw [Nat.add_assoc, Nat.add_lt_add_iff_left, Nat.add_comm]
    exact b_bound₀ (by decide) (by decide) b h1

/-- Final solution -/
theorem final_solution : good k n ↔ (k = 0 ∧ n = 0) ∨ (k = 2 ∧ n = 4) := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ : 2 ∣ k ∧ 2 ∣ n := good_imp_even h
    apply (good_two_mul_imp₂ (good_two_mul_imp₁ h)).imp
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, hb⟩; refine ⟨rfl, ?_⟩
      rw [Nat.le_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one] at hb
      unfold good at h; rcases hb with (rfl | rfl) | rfl
      · revert h; decide
      · revert h; decide
      · rfl
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [good_zero_zero, good_two_four]
