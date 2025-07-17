/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Positive.Ring
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# IMO 2022 A3 (P2)

Let $R$ be a totally ordered commutative ring, and let $R_{>0} = \{x ∈ R : x > 0\}$.
Find all functions $f : R_{>0} → R_{>0}$ such that for any $x ∈ R_{>0}$,
  there exists a unique $y ∈ R_{>0}$ such that $x f(y) + y f(x) ≤ 2$.
-/

namespace IMOSL
namespace IMO2022A3

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Extra lemmas -/

lemma add_sq_le_two_mul_imp [ExistsAddOfLE R] {x y : R} (h : x ^ 2 + y ^ 2 ≤ 2 * x * y) :
    x = y := by
  have X {x c : R} (h : x ^ 2 + (x + c) ^ 2 ≤ 2 * x * (x + c)) : c = 0 := by
    rw [add_sq, sq, ← add_assoc, ← add_assoc, ← two_mul,
      ← mul_assoc, ← mul_add, add_le_iff_nonpos_right] at h
    exact sq_eq_zero_iff.mp (h.antisymm (sq_nonneg c))
  obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ : (∃ c, y = x + c) ∨ (∃ c, x = y + c) :=
    (le_total x y).imp exists_add_of_le exists_add_of_le
  · rw [X h, add_zero]
  · rw [add_comm, mul_right_comm] at h
    rw [X h, add_zero]





/-! ### Start of the problem -/

/-- This definition does not even require `f(x) > 0` for `x > 0`.
  However, as we show below, the functional equation still only has at most one solution. -/
def weakGood (f : R → R) := ∀ x > 0, ∃! y > 0, x * f y + y * f x ≤ 2

theorem weakGood_iff [ExistsAddOfLE R] {f : R → R} : weakGood f ↔ ∀ x > 0, x * f x = 1 := by
  refine ⟨λ hf ↦ ?_, λ hf x hx ↦ ?_⟩
  ---- `→` direction
  · have hf0 {x} (hx : 0 < x) : x * f x ≤ 1 := by
      obtain ⟨y, ⟨hy, hy0⟩, h⟩ := hf x hx
      suffices x = y by
        rwa [← mul_one 2, ← this, ← two_mul, mul_le_mul_iff_of_pos_left two_pos] at hy0
      by_contra h0
      have h1 : 1 < x * f x := by
        rw [← mul_lt_mul_iff_of_pos_left two_pos, mul_one, two_mul]
        exact lt_of_not_ge λ h1 ↦ h0 (h x ⟨hx, h1⟩)
      have h2 : 1 < y * f y := by
        rw [← mul_lt_mul_iff_of_pos_left two_pos, mul_one, two_mul]
        refine lt_of_not_ge λ h2 ↦ h0 ((hf y hy).unique ⟨hx, ?_⟩ ⟨hy, h2⟩)
        rwa [add_comm] at hy0
      refine hy0.not_gt (lt_of_mul_lt_mul_of_nonneg_right ?_ (mul_pos hx hy).le)
      calc
        _ = 2 * x * y := (mul_assoc 2 x y).symm
        _ ≤ x ^ 2 + y ^ 2 := two_mul_le_add_sq x y
        _ < x ^ 2 * (y * f y) + y ^ 2 * (x * f x) :=
          add_lt_add (lt_mul_of_one_lt_right (pow_pos hx 2) h2)
            (lt_mul_of_one_lt_right (pow_pos hy 2) h1)
        _ = x * y * (x * f y) + y * x * (y * f x) := by
          apply congrArg₂ <;> rw [sq, mul_mul_mul_comm]
        _ = _ := by rw [mul_comm y x, ← mul_add, mul_comm]
    replace hf {x y} (hx : 0 < x) (hy : 0 < y) (h : x * f y + y * f x ≤ 2) : x = y := by
      refine (hf x hx).unique ⟨hx, ?_⟩ ⟨hy, h⟩
      have h0 := hf0 hx; exact (add_le_add h0 h0).trans_eq one_add_one_eq_two
    intro x hx; have h := hf0 hx
    obtain ⟨M, h0⟩ : ∃ M, 1 = x * f x + M := exists_add_of_le h
    suffices (1 + M) * x = x by
      rw [one_add_mul, add_eq_left, mul_eq_zero, or_iff_left hx.ne.symm] at this
      rw [h0, this, add_zero]
    replace h : 0 ≤ M := by rwa [h0, le_add_iff_nonneg_right] at h
    have h1 : 0 < 1 + M := add_pos_of_pos_of_nonneg one_pos h
    have h2 : 0 < (1 + M) * x := mul_pos h1 hx
    have h3 : x * f ((1 + M) * x) ≤ 1 := by
      rw [← mul_le_mul_iff_of_pos_left h1, ← mul_assoc, mul_one]
      exact le_add_of_le_of_nonneg (hf0 h2) h
    have h4 : (1 + M) * x * f x ≤ 1 := by calc
      _ ≤ (1 + M) * x * f x + M ^ 2 := le_add_of_nonneg_right (sq_nonneg M)
      _ = x * f x + M * (x * f x) + M ^ 2 := by rw [mul_assoc, one_add_mul]
      _ = x * f x + M * (x * f x + M) := by rw [add_assoc, sq, mul_add]
      _ = 1 := by rw [← h0, mul_one, ← h0]
    exact hf h2 hx ((add_le_add h4 h3).trans_eq one_add_one_eq_two)
  ---- `←` direction
  · refine ⟨x, ⟨hx, hf x hx ▸ one_add_one_eq_two.le⟩, λ y hy ↦ add_sq_le_two_mul_imp ?_⟩
    calc
      _ = x ^ 2 * (y * f y) + y ^ 2 * (x * f x) := by
        rw [add_comm, hf x hx, hf y hy.1, mul_one, mul_one]
      _ = x * y * (x * f y) + y * x * (y * f x) := by
        apply congrArg₂ <;> rw [sq, mul_mul_mul_comm]
      _ = (x * f y + y * f x) * (y * x) := by
        rw [mul_comm x, ← mul_add, mul_comm]
      _ ≤ 2 * (y * x) := mul_le_mul_of_nonneg_right hy.2 (mul_pos hy.1 hx).le
      _ = _ := (mul_assoc 2 y x).symm





/-! ### The main version -/

def posSubtypeExt (f : {x : R // 0 < x} → {x : R // 0 < x}) (x : R) : R :=
  dite (0 < x) (λ h ↦ f ⟨x, h⟩) (λ _ ↦ 0)

omit [IsStrictOrderedRing R] in
lemma posSubtypeExt_spec (f : {x : R // 0 < x} → {x : R // 0 < x}) (x : {x : R // 0 < x}) :
    posSubtypeExt f x.1 = f x :=
  dif_pos _

def good (f : {x : R // 0 < x} → {x : R // 0 < x}) :=
  ∀ x, ∃! y, x * f y + y * f x ≤ ⟨2, two_pos⟩

lemma good_iff_posSubtypeExt_weakGood {f : {x : R // 0 < x} → {x : R // 0 < x}} :
    good f ↔ weakGood (posSubtypeExt f) := by
  refine ⟨λ hf x hx ↦ ?_, λ hf x ↦ ?_⟩
  ---- `→` direction
  · lift x to {x : R // 0 < x} using hx
    obtain ⟨y, hy, hy0⟩ := hf x
    refine ⟨y.1, ⟨y.2, ?_⟩, λ z hz ↦ ?_⟩
    · rw [posSubtypeExt_spec, posSubtypeExt_spec]; exact hy
    · rcases hz with ⟨hz, hz0⟩; lift z to {x : R // 0 < x} using hz
      rw [posSubtypeExt_spec, posSubtypeExt_spec] at hz0
      exact congrArg _ (hy0 z hz0)
  ---- `←` direction
  · obtain ⟨y, ⟨hy, hy0⟩, hy1⟩ := hf x.1 x.2
    lift y to {x : R // 0 < x} using hy
    refine ⟨y, ?_, λ z hz ↦ ?_⟩
    · rwa [posSubtypeExt_spec, posSubtypeExt_spec] at hy0
    · refine Subtype.eq (hy1 z.1 ⟨z.2, ?_⟩)
      rwa [posSubtypeExt_spec, posSubtypeExt_spec]

/-- Final solution -/
theorem final_solution [ExistsAddOfLE R] {f : {x : R // 0 < x} → {x : R // 0 < x}} :
    good f ↔ ∀ x, x * f x = 1 := by
  rw [good_iff_posSubtypeExt_weakGood, weakGood_iff]
  refine ⟨λ h x ↦ ?_, λ h x hx ↦ ?_⟩
  · specialize h x.1 x.2
    rw [posSubtypeExt_spec] at h
    exact Subtype.eq h
  · lift x to {x : R // 0 < x} using hx
    rw [posSubtypeExt_spec]; exact congrArg (λ x ↦ x.1) (h x)
