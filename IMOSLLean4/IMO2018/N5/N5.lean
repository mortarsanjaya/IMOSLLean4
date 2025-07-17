/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# IMO 2018 N5

Determine whether there exists $x, y, z, t ∈ ℕ^+$ such that
  $xy - zt = x + y = z + t$ and both $xy$ and $zt$ are perfect squares.
-/

namespace IMOSL
namespace IMO2018N5

/-! ### Extra lemmas -/

theorem even_mul_of_odd_add {x y : ℤ} (h : Odd (x + y)) : Even (x * y) := by
  rw [← Int.not_odd_iff_even, Int.odd_mul]
  rintro ⟨hx, hy⟩; exact Int.not_even_iff_odd.mpr h (hx.add_odd hy)

theorem sq_sub_eq_sq_bound {a b : ℤ} (hb : 0 < b) (h : ∃ c, a ^ 2 - b = c ^ 2) :
    2 * a - 1 ≤ b := by
  wlog ha : 0 ≤ a generalizing a
  · replace ha : a ≤ 0 := Int.le_of_not_le ha
    have ha' : 0 ≤ -a := Int.neg_nonneg_of_nonpos ha
    apply (this (neg_sq a ▸ h) ha').trans'
    exact Int.sub_le_sub_right (Int.mul_le_mul_of_nonneg_left (ha.trans ha') zero_le_two) _
  rcases h with ⟨c, h⟩
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h; subst b
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le',
    ← one_pow 2, ← (2 * a).mul_one, ← sub_add, ← sub_sq]
  replace ha : 0 < a := by
    refine ha.lt_or_eq.resolve_right λ h ↦ hb.not_ge ?_
    subst h; rw [sub_nonpos, sq, Int.zero_mul]
    exact sq_nonneg c
  wlog hc : 0 ≤ c generalizing c
  · exact neg_sq c ▸ this _ (neg_sq c ▸ hb) (Int.neg_nonneg_of_nonpos (Int.le_of_not_le hc))
  replace hb : c < a := lt_of_pow_lt_pow_left₀ 2 ha.le (lt_of_sub_pos hb)
  exact pow_le_pow_left₀ hc (Int.le_sub_one_of_lt hb) 2





/-! ### General theory of good quadruplet -/

def good (v : Fin 4 → ℤ) := v 0 * v 1 - v 2 * v 3 = v 0 + v 1 ∧ v 0 + v 1 = v 2 + v 3

def mkGood (k l : ℤ) : Fin 4 → ℤ :=
  ![2 * (k * l) + (k - l), 2 * (k * l) - (k - l),
    2 * (k * l) + (k + l), 2 * (k * l) - (k + l)]

def mkGood_good (k l : ℤ) : good (mkGood k l) := by
  show (_ + _) * (_ - _) - (_ + _) * (_ - _) = (_ + _) + (_ - _)
    ∧ (_ + _) + (_ - _) = (_ + _) + (_ - _)
  rw [← sq_sub_sq, ← sq_sub_sq, sub_sub_sub_cancel_left, sq_sub_sq]
  simp only [add_add_sub_cancel]; refine ⟨?_, trivial⟩
  rw [add_sub_sub_cancel, ← two_mul, ← two_mul, ← two_mul, mul_mul_mul_comm, mul_assoc]

theorem good.eq_mkGood (hv : good v) : ∃ k l, v = mkGood k l := by
  obtain ⟨s, hs⟩ : 2 ∣ v 0 + v 1 := by
    refine even_iff_two_dvd.mp ((v 0 + v 1).even_or_odd.elim id λ h ↦ ?_)
    have h0 : Even (v 2 * v 3) := even_mul_of_odd_add (hv.2 ▸ h)
    replace h : Even (v 0 * v 1) := even_mul_of_odd_add h
    exact hv.1 ▸ h.sub h0
  obtain ⟨q, hq2, hq3⟩ : ∃ q, v 2 = s + q ∧ v 3 = s - q := by
    refine ⟨s - v 3, ?_, (Int.sub_sub_self _ _).symm⟩
    rw [← add_sub_assoc, ← two_mul, ← hs, hv.2, add_sub_cancel_right]
  obtain ⟨p, hp0, hp1⟩ : ∃ p, v 0 = s + p ∧ v 1 = s - p := by
    refine ⟨s - v 1, ?_, (Int.sub_sub_self _ _).symm⟩
    rw [← add_sub_assoc, ← two_mul, ← hs, add_sub_cancel_right]
  replace hs : q ^ 2 - p ^ 2 = 2 * s := calc
    _ = (s ^ 2 - p ^ 2) - (s ^ 2 - q ^ 2) := (sub_sub_sub_cancel_left _ _ _).symm
    _ = v 0 * v 1 - v 2 * v 3 := by rw [sq_sub_sq, hp0, hp1, sq_sub_sq, hq2, hq3]
    _ = _ := hv.1.trans hs
  obtain ⟨l, hl⟩ : 2 ∣ q - p := by
    have h : Even (q ^ 2 - p ^ 2) := hs ▸ even_two_mul s
    have X : 2 ≠ 0 := Nat.succ_ne_zero 1
    rw [Int.even_sub, Int.even_pow' X, Int.even_pow' X, ← Int.even_sub] at h
    exact even_iff_two_dvd.mp h
  obtain ⟨k, hk⟩ : 2 ∣ q + p := ⟨l + p, by rw [mul_add, ← hl, two_mul, sub_add_add_cancel]⟩
  have X : (2 : ℤ) ≠ 0 := OfNat.ofNat_ne_zero 2
  replace hs : 2 * (k * l) = s := by
    rw [sq_sub_sq, hk, hl, mul_mul_mul_comm, mul_assoc] at hs
    exact mul_left_cancel₀ X hs
  replace hl : p = k - l := by
    apply mul_left_cancel₀ X; rw [mul_sub, ← hk, ← hl, add_sub_sub_cancel, two_mul]
  replace hk : q = k + l := by rw [eq_sub_of_add_eq hk, hl, two_mul, add_sub_sub_cancel]
  subst s p q; refine ⟨k, l, funext λ x ↦ ?_⟩
  match x with | 0 => exact hp0 | 1 => exact hp1 | 2 => exact hq2 | 3 => exact hq3

theorem good_iff_eq_mkGood : good v ↔ ∃ k l, v = mkGood k l :=
  ⟨good.eq_mkGood, λ ⟨k, l, h⟩ ↦ h ▸ mkGood_good k l⟩

lemma mkGood_prod (k l) :
    (mkGood k l 0 * mkGood k l 1) * (mkGood k l 2 * mkGood k l 3)
      = ((2 * (k * l)) ^ 2 - (k ^ 2 + l ^ 2)) ^ 2 - (2 * (k * l)) ^ 2 := calc
  (2 * (k * l) + (k - l)) * (2 * (k * l) - (k - l))
    * ((2 * (k * l) + (k + l)) * (2 * (k * l) - (k + l)))
  _ = ((2 * (k * l)) ^ 2 - (k ^ 2 + l ^ 2 - 2 * (k * l)))
      * ((2 * (k * l)) ^ 2 - (k ^ 2 + l ^ 2 + 2 * (k * l))) := by
    rw [← sq_sub_sq, ← sq_sub_sq, sub_sq', add_sq', mul_assoc]
  _ = _ := by rw [← sub_sub, ← sub_add, ← sq_sub_sq]


variable (hv : good v)
include hv

theorem good.prod_eq_sq_imp' (h : ∃ a, (v 0 * v 1) * (v 2 * v 3) = a ^ 2) :
    (∃ x z, v = ![x, -x, z, -z])
      ∨ (v = ![2, 2, 4, 0] ∨ v = ![0, -4, -2, -2])
      ∨ (v = ![-4, 0, -2, -2] ∨ v = ![2, 2, 0, 4]) := by
  rw [good_iff_eq_mkGood] at hv; rcases hv with ⟨k, l, rfl⟩
  refine (dec_em ((2 * (k * l)) = 0)).imp (λ h0 ↦ ?_) (λ h0 ↦ ?_)
  ---- Case 1: `2kl = 0`
  · rw [mkGood, h0, zero_add, zero_add, zero_sub, zero_sub]
    exact ⟨k - l, k + l, rfl⟩
  ---- Case 2: `2kl ≠ 0`
  · replace h : 2 * ((2 * (k * l)) ^ 2 - (k ^ 2 + l ^ 2)) - 1 ≤ (2 * (k * l)) ^ 2 :=
      sq_sub_eq_sq_bound (sq_pos_of_ne_zero h0) (mkGood_prod _ _ ▸ h)
    replace h0 : 0 < k ^ 2 ∧ 0 < l ^ 2 := by
      rw [← Ne, mul_ne_zero_iff, mul_ne_zero_iff] at h0
      exact h0.2.imp sq_pos_of_ne_zero sq_pos_of_ne_zero
    rw [Int.mul_sub, Int.two_mul, sub_sub, sub_le_iff_le_add, add_le_add_iff_left,
      ← Int.lt_add_one_iff, Int.add_assoc, mul_pow, sq, mul_assoc, mul_pow] at h
    replace h : k ^ 2 * l ^ 2 + k ^ 2 * l ^ 2 ≤ k ^ 2 + l ^ 2 := by
      refine Int.le_of_lt_add_one (Int.lt_of_mul_lt_mul_left ?_ zero_le_two)
      rwa [← two_mul, mul_add_one]
    have h1 : k = 1 ∨ k = -1 := by
      refine sq_eq_one_iff.mp (h0.1.antisymm ?_).symm
      replace h : k ^ 2 * l ^ 2 ≤ l ^ 2 := by
        refine le_of_add_le_add_left (h.trans' ?_)
        exact add_le_add_right (le_mul_of_one_le_right h0.1.le h0.2) _
      rw [← sub_nonpos, ← sub_one_mul] at h
      exact Int.le_add_of_sub_right_le (nonpos_of_mul_nonpos_left h h0.2)
    replace h : l = 1 ∨ l = -1 := by
      refine sq_eq_one_iff.mp (h0.2.antisymm ?_).symm
      replace h : k ^ 2 * l ^ 2 ≤ k ^ 2 := by
        refine le_of_add_le_add_right (h.trans' ?_)
        exact add_le_add_left (le_mul_of_one_le_left h0.2.le h0.1) _
      rw [← sub_nonpos, ← mul_sub_one] at h
      exact Int.le_add_of_sub_right_le (nonpos_of_mul_nonpos_right h h0.1)
    revert h1; apply Or.imp
    all_goals rintro rfl; revert h; apply Or.imp
    all_goals rintro rfl; rfl

theorem good.prod_eq_sq_imp (h : ∃ a, v 0 * v 1 = a ^ 2) (h0 : ∃ b, v 2 * v 3 = b ^ 2) :
    v = ![0, 0, 0, 0] ∨ (v = ![2, 2, 4, 0] ∨ v = ![0, -4, -2, -2])
      ∨ (v = ![-4, 0, -2, -2] ∨ v = ![2, 2, 0, 4]) := by
  rcases h with ⟨a, h⟩; rcases h0 with ⟨b, h0⟩
  apply (hv.prod_eq_sq_imp' ⟨a * b, by rw [h, h0, mul_pow]⟩).imp_left
  rintro ⟨x, z, rfl⟩; suffices x = 0 ∧ z = 0 by rcases this with ⟨rfl, rfl⟩; rfl
  refine ⟨?_, ?_⟩
  ---- `x = 0`
  · replace h : 0 ≤ x * -x := h ▸ sq_nonneg a
    rw [mul_neg, neg_nonneg, ← sq] at h
    exact sq_eq_zero_iff.mp (h.antisymm (sq_nonneg x))
  ---- `z = 0`
  · replace h0 : 0 ≤ z * -z := h0 ▸ sq_nonneg b
    rw [mul_neg, neg_nonneg, ← sq] at h0
    exact sq_eq_zero_iff.mp (h0.antisymm (sq_nonneg z))

/-- Final solution -/
theorem final_solution (hv0 : ∀ i, v i ≠ 0) :
    ¬((∃ x, v 0 * v 1 = x ^ 2) ∧ ∃ y, v 2 * v 3 = y ^ 2) := by
  rintro ⟨h, h0⟩
  obtain rfl | ((rfl | rfl) | (rfl | rfl)) := hv.prod_eq_sq_imp h h0
  exacts [hv0 0 rfl, hv0 3 rfl, hv0 0 rfl, hv0 1 rfl, hv0 2 rfl]
