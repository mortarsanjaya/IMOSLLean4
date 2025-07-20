/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Prime.Basic

/-!
# IMO 2023 N2

Find all pairs $(a, p) ∈ ℕ^2$ with $a > 0$ and $p$ prime
  such that $p^a + a^4$ is a perfect square.
-/

namespace IMOSL
namespace IMO2023N2

/-! ### Some bounding -/

lemma y_ineq₁ (hy : 3 ≤ y) : (y + 2) ^ 2 < 3 * y ^ 2 := by
  rw [Nat.succ_mul, add_sq, Nat.add_assoc, Nat.add_comm, Nat.add_lt_add_iff_right,
    sq, ← Nat.add_mul, Nat.mul_comm, Nat.mul_lt_mul_left Nat.two_pos, sq]
  apply (Nat.add_le_add_left hy _).trans ((Nat.succ_mul 2 y).ge.trans ?_)
  exact Nat.mul_le_mul_right y hy

lemma y_ineq₂ (hy : 5 ≤ y) : (y + 2) ^ 2 < 2 * y ^ 2 := by
  rw [Nat.two_mul, add_sq, Nat.mul_right_comm, Nat.add_assoc, Nat.add_lt_add_iff_left]
  apply (Nat.add_lt_add_left hy _).trans_le
  rw [← Nat.succ_mul, sq]
  exact Nat.mul_le_mul_right y hy

lemma y_bound₀ (hn : 0 < n) (hp : 3 ≤ p) (h : 2 * (2 * n + 1) ^ 2 < k * p ^ n) (hy : n ≤ y) :
    2 * (2 * y + 1) ^ 2 < k * p ^ y := by
  induction y, hy using Nat.le_induction with | base => exact h | succ y hy h0 => ?_
  calc 2 * (2 * y + 1 + 2) ^ 2
    _ < 2 * (3 * (2 * y + 1) ^ 2) := ?_
    _ = 3 * (2 * (2 * y + 1) ^ 2) := Nat.mul_left_comm _ _ _
    _ ≤ p * (k * p ^ y) := Nat.mul_le_mul hp h0.le
    _ = k * (p ^ y * p) := mul_rotate' _ _ _
  refine Nat.mul_lt_mul_of_pos_left (y_ineq₁ ?_) Nat.two_pos
  exact Nat.succ_le_succ (Nat.mul_le_mul_left 2 (hn.trans_le hy))

lemma y_bound₁ (hp : 5 ≤ p) (y) : 2 * (2 * y + 1) ^ 2 < (p - 1) * p ^ y := by
  have hp0 : 3 < p := hp.trans_lt' (by decide)
  rcases y with _ | y
  ---- Case 1: `y - 0`
  · rwa [p.pow_zero, Nat.mul_one, Nat.lt_sub_iff_add_lt]
  ---- Case 2: `y > 0`, write `y` as `y + 1`
  · refine y_bound₀ Nat.one_pos hp0.le ?_ y.succ_pos
    rw [p.pow_one]; exact (Nat.mul_le_mul (Nat.pred_le_pred hp) hp).trans_lt' (by decide)

lemma y_bound₂ (hy : 10 ≤ y) : 2 * (2 * y + 1) ^ 2 < 2 ^ y := by
  induction y, hy using Nat.le_induction with | base => decide | succ y hy h0 => ?_
  calc 2 * (2 * y + 1 + 2) ^ 2
    _ < 2 * (2 * (2 * y + 1) ^ 2) := ?_
    _ ≤ 2 * 2 ^ y := Nat.mul_le_mul_left 2 h0.le
    _ = 2 ^ (y + 1) := Nat.pow_succ'.symm
  refine Nat.mul_lt_mul_of_pos_left (y_ineq₂ (Nat.succ_le_succ ?_)) Nat.two_pos
  exact Nat.mul_le_mul_left 2 (Nat.le_of_add_right_le (k := 8) hy)





/-! ### Start of the problem -/

def good (a p : ℕ) := ∃ b, p ^ a + a ^ 4 = b ^ 2

def good_alt (x y p : ℕ) := p ^ x + 2 * (x + y) ^ 2 = p ^ y

lemma good_imp_alt (hp : Nat.Prime p) (h : good a p) :
    ∃ x y, a = x + y ∧ good_alt x y p := by
  rcases h with ⟨b, h⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = c + a ^ 2 := by
    apply Nat.exists_eq_add_of_le'
    rw [← Nat.mul_self_le_mul_self_iff, ← sq, ← sq, ← Nat.pow_mul, ← h]
    exact Nat.le_add_left _ _
  rw [add_sq, ← Nat.pow_mul, Nat.add_left_inj, sq, Nat.mul_right_comm, ← Nat.add_mul] at h
  obtain ⟨x, ⟨y, rfl⟩, rfl⟩ : ∃ x, (∃ y, a = x + y) ∧ c = p ^ x := by
    obtain ⟨x, hx, rfl⟩ : ∃ x ≤ a, c = p ^ x :=
      (Nat.dvd_prime_pow hp).mp (h ▸ c.dvd_mul_left _)
    exact ⟨x, Nat.exists_eq_add_of_le hx, rfl⟩
  rw [Nat.pow_add, Nat.mul_comm] at h
  exact ⟨x, y, rfl, Nat.mul_right_cancel (Nat.pow_pos hp.pos) h.symm⟩

lemma good_alt_imp (hxy : 0 < x + y) (h : good_alt x y p) :
    p = 3 ∧ (x + y = 1 ∨ x + y = 2 ∨ x + y = 6 ∨ x + y = 9) := by
  replace hxy : 1 < 2 * (x + y) ^ 2 := Nat.le_mul_of_pos_right 2 (Nat.pow_pos hxy)
  have hp : 1 < p ^ y := h ▸ (hxy.trans_le (Nat.le_add_left _ _))
  match y with | 0 => exact absurd rfl hp.ne | y + 1 => ?_
  replace hp : 1 < p := (Nat.one_lt_pow_iff y.succ_ne_zero).mp hp
  replace hxy : x ≤ y := by
    rw [← Nat.lt_succ, ← Nat.pow_lt_pow_iff_right hp, ← h, Nat.lt_add_right_iff_pos]
    exact Nat.zero_lt_of_lt hxy
  have h0 : (p - 1) * p ^ y ≤ 2 * (2 * y + 1) ^ 2 := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_succ', ← h, Nat.add_comm]
    refine Nat.sub_le_of_le_add (Nat.add_le_add ?_ ?_)
    · rw [y.two_mul, Nat.add_assoc]
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.add_le_add_right hxy _) 2)
    · exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp) hxy
  replace hp : 2 = p ∨ 3 = p ∨ 4 = p ∨ 5 ≤ p := by
    simpa only [Nat.succ_le, ← le_iff_eq_or_lt]
  rcases hp with rfl | rfl | rfl | hp
  ---- Case 1: `p = 2`
  · replace h0 : y < 10 := Nat.lt_of_not_le λ h1 ↦
      h0.not_gt ((y_bound₂ h1).trans_eq (Nat.one_mul _).symm)
    exfalso; revert x; revert y
    unfold good_alt; decide
  ---- Case 2: `p = 3`
  · replace h0 : y < 5 := Nat.lt_of_not_le λ h1 ↦
      h0.not_gt (y_bound₀ (by decide) (by decide) (by decide) h1)
    revert x; revert y
    unfold good_alt; decide
  ---- Case 3: `p = 4`
  · replace h0 : y < 3 := Nat.lt_of_not_le λ h1 ↦
      h0.not_gt (y_bound₀ (by decide) (by decide) (by decide) h1)
    exfalso; revert x; revert y
    unfold good_alt; decide
  ---- Case 4: `p ≥ 5`
  · exact absurd (y_bound₁ hp y) h0.not_gt

/-- Final solution -/
theorem final_solution {a p : ℕ} (ha : 0 < a) (hp : p.Prime) :
    good a p ↔ p = 3 ∧ (a = 1 ∨ a = 2 ∨ a = 6 ∨ a = 9) := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  ---- `←` direction
  · obtain ⟨x, y, rfl, h0⟩ : ∃ x y, a = x + y ∧ good_alt x y p := good_imp_alt hp h
    exact good_alt_imp ha h0
  ---- `→` direction
  · rcases h with ⟨rfl, rfl | rfl | rfl | rfl⟩
    exacts [⟨2, rfl⟩, ⟨5, rfl⟩, ⟨45, rfl⟩, ⟨162, rfl⟩]
