/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Rat.Floor

/-!
# IMO 2013 N6

Determine all functions $f : ℚ → ℤ$ such that for any $x ∈ ℚ$, $a ∈ ℤ$, and $b ∈ ℕ^+$,
$$ f\left(\frac{f(x) + a}{b}\right) = f\left(\frac{x + a}{b}\right). $$
-/

namespace IMOSL
namespace IMO2013N6

def good (f : ℚ → ℤ) :=
    ∀ (x : ℚ) (a : ℤ) (b : ℕ), 0 < b → f ((f x + a) / b) = f ((x + a) / b)



theorem good_const (C : ℤ) : good (λ _ ↦ C) := λ _ _ _ _ ↦ rfl

theorem good_floor : good Int.floor := λ x a b hb ↦ by
  refine Int.floor_congr λ n ↦ ?_
  replace hb : 0 < (b : ℚ) := Nat.cast_pos.mpr hb
  rw [← Int.cast_add, ← Int.floor_add_intCast, le_div_iff₀ hb, le_div_iff₀ hb,
    ← Int.cast_natCast, ← Int.cast_mul, Int.cast_le, Int.le_floor]

theorem good_neg_map_neg (hf : good f) : good (λ x ↦ -f (-x)) := λ x a b hb ↦ by
  rw [Int.cast_neg, neg_inj, ← neg_div, neg_add, neg_neg,
    ← a.cast_neg, hf _ _ b hb, Int.cast_neg, ← neg_add, neg_div]

theorem good_ceil : good Int.ceil :=
  good_neg_map_neg good_floor





section

variable (hf : good f)
include hf

lemma const_of_not_int_id {n : ℤ} (h : f n ≠ n) : ∃ C, f = λ _ ↦ C := by
  rw [← sub_ne_zero] at h
  have h0 (k : ℤ) : f (k + ↑(f n - n) / |f n - n|) = f k := by
    specialize hf n (k * |f n - n| - n) _ (Int.natAbs_pos.mpr h)
    rw [← abs_ne_zero, ← Int.cast_ne_zero (α := ℚ)] at h
    rwa [Int.cast_sub, add_sub_cancel, Int.cast_mul, add_sub_left_comm,
      Int.cast_natAbs, add_div, mul_div_cancel_right₀ _ h, ← Int.cast_sub] at hf
  replace h0 (k : ℤ) : f (k + 1) = f k := by
    generalize f n - n = t at h h0
    have h1 : (t : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h
    obtain h2 | h2 := le_total 0 t
    · specialize h0 k; rwa [abs_eq_self.mpr h2, div_self h1] at h0
    · specialize h0 (k + 1)
      rwa [abs_eq_neg_self.mpr h2, Int.cast_neg, div_neg, div_self h1,
        Int.cast_add, Int.cast_one, add_neg_cancel_right, eq_comm] at h0
  replace h0 (k : ℤ) : f k = f 0 := by
    refine Int.inductionOn' k 0 rfl (λ k _ h ↦ ?_) (λ k _ h ↦ ?_)
    · rw [Int.cast_add, Int.cast_one, h0, h]
    · rw [← h0, Int.cast_sub, Int.cast_one, sub_add_cancel, h]
  ---- Now finish
  refine ⟨f 0, funext λ x ↦ ?_⟩
  specialize hf x 0 1 Nat.one_pos
  rwa [Nat.cast_one, div_one, div_one, Int.cast_zero, add_zero, h0, add_zero, eq_comm] at hf

variable (h : ∀ n : ℤ, f n = n)
include h

lemma int_id_map_add_int (x : ℚ) (a : ℤ) : f (x + a) = f x + a := by
  specialize hf x a 1 Nat.one_pos
  rwa [Nat.cast_one, div_one, div_one, ← Int.cast_add, h, eq_comm] at hf

lemma eq_floor_of_map_half_nonpos (h0 : f 2⁻¹ ≤ 0) : f = Int.floor := by
  suffices ∀ x : ℚ, 0 ≤ x → x < 1 → f x = 0 from funext λ x ↦ by
    rw [← add_neg_eq_zero, ← int_id_map_add_int hf h, Int.cast_neg, ← sub_eq_add_neg]
    exact this _ (Int.fract_nonneg x) (Int.fract_lt_one x)
  suffices ∀ m k : ℕ, k < m → f (k / m) = 0 from λ x h1 h2 ↦ by
    replace h1 : |x.num| = x.num := abs_eq_self.mpr (Rat.num_nonneg.mpr h1)
    replace h2 : x.num.natAbs < x.den := by
      rw [← Int.ofNat_lt, Int.natCast_natAbs, h1]
      rw [← x.num_div_den, div_lt_one (Nat.cast_pos.mpr x.den_pos)] at h2
      exact Int.cast_lt.mp h2
    specialize this x.den x.num.natAbs h2
    rwa [Int.cast_natAbs, h1, Rat.num_div_den] at this
  replace h0 : f 2⁻¹ = 0 := by
    replace h0 : 0 < 1 - 2 * f 2⁻¹ := by
      rw [sub_pos, ← Int.zero_add 1, Int.lt_add_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos zero_le_two h0
    specialize hf 2⁻¹ (-f 2⁻¹) (1 - 2 * f 2⁻¹).natAbs (Int.natAbs_pos.mpr h0.ne.symm)
    rw [Int.cast_neg, add_neg_cancel, zero_div, Int.cast_natAbs, abs_eq_self.mpr h0.le,
      inv_eq_one_div, ← sub_eq_add_neg, div_sub' two_ne_zero, one_div] at hf
    have h1 : (1 - 2 * f 2⁻¹ : ℚ) = (1 - 2 * f 2⁻¹ : ℤ) := by
      rw [Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_two]
    rwa [h1, div_right_comm, div_self (Int.cast_ne_zero.mpr h0.ne.symm),
      one_div, ← Int.cast_zero, h, eq_comm] at hf
  ---- Start the induction, immediately resolving the base case
  refine Nat.rec (λ k h1 ↦ h1.not_ge.elim k.zero_le) (λ m hm ↦ ?_)
  replace hm (k) (h1 : k < m) : f (k / m.succ) = 0 := by
    specialize hf (k / m) k m.succ m.succ_pos
    have h2 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt h1)
    have h3 : (m.succ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr m.succ_ne_zero
    rwa [Int.cast_natCast, div_add' _ _ _ h2, add_comm (k : ℚ),
      ← Nat.cast_mul, div_div, ← Nat.cast_add, ← Nat.mul_succ, Nat.cast_mul,
      mul_div_mul_right _ _ h3, hm k h1, Int.cast_zero, zero_add] at hf
  simp only [Nat.lt_succ_iff_lt_or_eq]; rintro k (h2 | rfl)
  · exact hm k h2
  ---- Remaining case to solve: `f(k/(k + 1)) = 0`
  rcases k with _ | k
  · rw [Nat.cast_one, div_one, Nat.cast_zero, ← Int.cast_zero, h]
  specialize hf (k / k.succ.succ) 1 2 Nat.two_pos
  rwa [hm k k.lt_succ_self, Int.cast_zero, zero_add, Int.cast_one, Nat.cast_two,
    one_div, h0, div_add_one (Nat.cast_ne_zero.mpr (k + 1).succ_ne_zero),
    Nat.cast_succ, div_div, add_left_comm, ← Nat.cast_succ, ← mul_two,
    mul_div_mul_right _ _ two_ne_zero, eq_comm, ← Nat.cast_succ] at hf

end





/-- Final solution -/
theorem final_solution : good f ↔ (∃ C, f = λ _ ↦ C) ∨ f = Int.floor ∨ f = Int.ceil := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  ---- `→` direction
  · refine (em' (∀ n : ℤ, f n = n)).imp
      (λ h0 ↦ (not_forall.mp h0).elim λ n ↦ const_of_not_int_id h)
      (λ h0 ↦ (le_or_gt (f 2⁻¹) 0).imp (eq_floor_of_map_half_nonpos h h0) (λ h1 ↦ ?_))
    -- Only need to consider the case `f(1/2) > 0`.
    replace h : (λ x ↦ -f (-x)) = Int.floor := by
      refine eq_floor_of_map_half_nonpos (good_neg_map_neg h) (λ n ↦ ?_) ?_
      · rw [neg_eq_iff_eq_neg, ← Int.cast_neg, h0]
      · have h2 := int_id_map_add_int h h0 (-2⁻¹) 1
        rw [Int.cast_one, ← add_halves 1, one_div, neg_add_cancel_left] at h2
        rwa [neg_nonpos, ← Int.lt_add_one_iff, ← h2]
    funext x; rw [← neg_neg x, ← neg_inj, congrFun h,
      eq_comm, neg_eq_iff_eq_neg, neg_neg]; rfl
  ---- `←` direction
  · rcases h with ⟨C, rfl⟩ | rfl | rfl
    exacts [good_const C, good_floor, good_ceil]
