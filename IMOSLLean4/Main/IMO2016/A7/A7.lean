/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Group.Pi.Basic

/-!
# IMO 2016 A7

Let $R$ be a ring and $S$ be a totally ordered commutative ring.
Find all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(x + y)^2 = 2 f(x) f(y) + \max\{f(x^2) + f(y^2), f(x^2 + y^2)\}. $$
-/

namespace IMOSL
namespace IMO2016A7

section

variable [Semiring R]

def good [Semiring S] [LinearOrder S] (f : R → S) :=
  ∀ x y, f (x + y) ^ 2 = 2 * f x * f y + max (f (x ^ 2) + f (y ^ 2)) (f (x ^ 2 + y ^ 2))

lemma zero_is_good [Semiring S] [LinearOrder S] : good (λ _ : R ↦ (0 : S)) := λ x y ↦ by
  rw [zero_pow (Nat.succ_ne_zero 1), mul_zero, zero_add, add_zero, max_self]

lemma neg_one_is_good [Ring S] [LinearOrder S] [IsStrictOrderedRing S] :
    good (λ _ : R ↦ (-1 : S)) := λ x y ↦ by
  rw [mul_assoc, ← sq, neg_one_sq, two_mul, add_assoc, left_eq_add,
    ← max_add_add_left, ← add_assoc, add_neg_cancel, zero_add, max_eq_right_iff]
  exact neg_one_lt_zero.le

lemma hom_is_good [CommSemiring S] [LinearOrder S] (φ : R →+* S) : good φ := λ x y ↦ by
  rw [φ.map_add, φ.map_add, max_self, add_comm (_ * _), φ.map_pow, φ.map_pow, add_sq']

lemma hom_sub_one_is_good [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (φ : R →+* S) : good (φ · - 1) := λ x y ↦ by
  simp only [φ.map_add, φ.map_pow]
  rw [sub_add_sub_comm, ← sub_sub, max_eq_right (sub_le_self _ (zero_le_one' S)), sub_sq,
    one_pow, mul_one, mul_sub_one 2, mul_sub_one, sub_mul, sub_sub, add_comm (_ * _ - _),
    sub_add_sub_comm, ← add_sq', sub_add, sub_right_inj, add_comm 1, ← add_sub_assoc,
    ← mul_add, add_comm, sub_add, sub_right_inj, ← one_add_one_eq_two, add_sub_cancel_right]

/-- Solver for `f(x + y) = f(x) + f(y)` and `f(x^2) = f(x)^2` -/
theorem eq_zero_or_hom_of_map_add_map_sq [CommRing S] [IsDomain S] [CharZero S] {f : R → S}
    (h : ∀ x y : R, f (x + y) = f x + f y) (h0 : ∀ x : R, f (x ^ 2) = f x ^ 2) :
    f = 0 ∨ ∃ φ : R →+* S, f = φ := by
  suffices ∀ x y, f (x * y) = f x * f y by
    have h1 : f 1 = 0 ∨ f 1 = 1 := by
      specialize h0 1; rwa [one_pow, sq, ← sub_eq_zero, ← one_sub_mul,
        mul_eq_zero, sub_eq_zero, eq_comm, or_comm] at h0
    revert h1; refine Or.imp (λ h1 ↦ ?_) (λ h1 ↦ ⟨RingHom.mk' ⟨⟨f, h1⟩, this⟩ h, rfl⟩)
    funext x; rw [← mul_one x, this, h1, mul_zero]; rfl
  have h1 (x y) : f (x * y) + f (y * x) = 2 * (f x * f y) := by
    have h1 := h0 (x + y)
    rwa [h, add_sq, sq, add_mul, mul_add, mul_add, h, h, h, ← sq, h0, ← sq,
      h0, ← add_assoc, add_left_inj, add_assoc, add_right_inj, mul_assoc] at h1
  have X : (2 : S) ≠ 0 := (OfNat.zero_ne_ofNat 2).symm
  intro x y; have h2 : f (x * y * x) = f x ^ 2 * f y := by
    have h2 : _ + _ = _ + _ := congrArg₂ _ (h1 x (x * y)) (h1 (y * x) x)
    rwa [add_add_add_comm, mul_assoc, ← mul_assoc, h1, ← sq, h0, ← mul_assoc x,
      ← two_mul, ← mul_add, ← mul_add, mul_comm (f (y * x)), ← sub_eq_zero,
      ← mul_sub, mul_eq_zero, ← mul_add, h1, mul_left_comm, ← mul_assoc (f x),
      ← sq, two_mul, or_iff_right X, add_sub_add_left_eq_sub, sub_eq_zero] at h2
  replace h2 : f (x * y) ^ 2 + f (y * x) ^ 2 = 2 * (f x * f y) ^ 2 := by
    specialize h1 (x * y * x) y; rwa [h2, mul_assoc, ← sq, h0, mul_assoc,
      ← mul_assoc, ← sq, h0, mul_assoc, ← sq, ← mul_pow] at h1
  replace h2 : f (x * y) = f (y * x) := by
    refine eq_of_sub_eq_zero (pow_eq_zero (n := 2) ?_)
    have h3 : _ ^ 2 = _ ^ 2 := congrArg₂ _ (h1 x y) rfl
    rw [add_sq', h2, mul_pow 2, sq 2, mul_assoc 2 2, two_mul (2 * _), add_right_inj] at h3
    rw [sub_sq', h2, h3, sub_self]
  specialize h1 x y
  rw [← h2, ← two_mul, ← sub_eq_zero, ← mul_sub, mul_eq_zero, or_iff_right X] at h1
  exact eq_of_sub_eq_zero h1

theorem good_map_zero [Ring S] [LinearOrder S] [IsStrictOrderedRing S]
    {f : R → S} (hf : good f) : f 0 = 0 ∨ f 0 = -1 := by
  specialize hf 0 0
  rw [zero_pow (Nat.succ_ne_zero 1), add_zero, mul_assoc, ← sq,
    two_mul, add_assoc, left_eq_add, ← neg_eq_iff_add_eq_zero] at hf
  have h : f 0 ≤ 0 := le_of_max_le_right (hf.symm.trans_le (neg_nonpos.mpr (sq_nonneg _)))
  rwa [max_eq_right (add_le_of_nonpos_left h), sq, neg_eq_iff_add_eq_zero,
    ← mul_add_one (f 0), mul_eq_zero, ← eq_neg_iff_add_eq_zero] at hf

theorem good_map_main_ineq [Ring S] [LinearOrder S] [IsOrderedRing S]
    {f : R → S} (hf : good f) (x y : R) :
    2 * f x * f y + (f (x ^ 2) + f (y ^ 2)) ≤ f (x + y) ^ 2 :=
  (add_le_add_left (le_max_left _ _) _).trans_eq (hf x y).symm

end





variable [Ring R] [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] {f : R → S}

/-- Solution for Case 1: `f(0) = 0` -/
theorem good_case_one (hf : good f) (h : f 0 = 0) : f = 0 ∨ ∃ φ : R →+* S, f = φ := by
  have h0 (x) : f (x ^ 2) = f x ^ 2 := by
    specialize hf x 0; rwa [add_zero, zero_pow (Nat.succ_ne_zero 1), h,
      mul_zero, add_zero, add_zero, max_self, zero_add, eq_comm] at hf
  suffices h1 : ∀ x y, f (x + y) = f x + f y from eq_zero_or_hom_of_map_add_map_sq h1 h0
  replace h0 {x y z} (h1 : x + y + z = 0) : (f x + f y + f z) * (f x + f y - f z) ≤ 0 := by
    rw [← sq_sub_sq, sub_nonpos, ← h0, ← neg_sq z, add_sq',
      ← eq_neg_of_add_eq_zero_left h1, h0, ← h0, ← h0, add_comm]
    exact good_map_main_ineq hf x y
  replace h0 {x y z} (h1 : x + y + z = 0) : f x + f y + f z = 0 := by
    have h2 := add_le_of_le_of_nonpos (h0 h1) (h0 ((add_rotate _ _ _).trans h1))
    rw [← add_rotate, ← mul_add, add_sub_assoc, add_sub_assoc,
      add_add_add_comm, sub_add_sub_cancel', add_add_sub_cancel] at h2
    replace h2 := add_le_of_le_of_nonpos h2 (h0 ((add_rotate _ _ _).symm.trans h1))
    rw [← add_rotate, ← mul_add, add_add_sub_cancel, ← add_rotate, ← add_assoc, ← sq] at h2
    exact sq_eq_zero_iff.mp (h2.antisymm (sq_nonneg _))
  replace h (x) : f (-x) = -f x := by
    specialize h0 ((add_zero _).trans (add_neg_cancel x))
    rwa [h, add_zero, add_comm, ← eq_neg_iff_add_eq_zero] at h0
  intro x y; specialize h0 (add_neg_cancel (x + y))
  rwa [h, add_neg_eq_zero, eq_comm] at h0

/-- Solution for Case 2: `f(0) = -1` -/
theorem good_case_two (hf : good f) (h : f 0 = -1) : f = -1 ∨ ∃ φ : R →+* S, f = φ - 1 := by
  have h0 (x) : f (x ^ 2) = f x ^ 2 + 2 * f x := by
    specialize hf x 0
    have X : (-1 : S) ≤ 0 := neg_one_lt_zero.le
    rw [add_zero, zero_pow (Nat.succ_ne_zero 1), h, mul_neg_one, eq_neg_add_iff_add_eq,
      add_zero, add_comm, max_eq_right (add_le_of_nonpos_right X)] at hf
    exact hf.symm
  suffices h1 : ∀ x y, f (x + y) + 1 = (f x + 1) + (f y + 1) by
    rw [eq_neg_iff_add_eq_zero (G := R → S)]; simp only [eq_sub_iff_add_eq]
    refine eq_zero_or_hom_of_map_add_map_sq h1 λ x ↦ ?_
    change f (x ^ 2) + 1 = (f x + 1) ^ 2; rw [h0, add_sq, mul_one, one_pow]
  have h1 {t} (ht : f (-t) = f t) : f t < 1 := by
    have h1 := good_map_main_ineq hf t (-t)
    rw [neg_sq, h0, ht, add_neg_cancel, h, neg_one_sq, ← two_mul, mul_assoc, ← sq,
      mul_add, ← add_assoc, ← two_mul, ← mul_assoc, ← mul_assoc, ← sq, ← mul_pow] at h1
    replace h := le_of_add_le_of_nonneg_right h1 (sq_nonneg _)
    refine lt_of_mul_lt_mul_of_nonneg_left (h.trans_lt ?_) (sq_nonneg 2)
    have X : (1 : S) < 2 := one_lt_two
    rw [mul_one, sq]; exact one_lt_mul X.le X
  rcases em' (∀ t, f (-t) = f t) with h2 | h2
  ---- Case 1: `f` is not even
  · replace h (x y) : f (x + y) - f (-(x + y)) = f (-x) * f (-y) - f x * f y := by
      have h3 := h0 (-(x + y))
      rw [neg_sq, neg_add, h0, add_comm, ← sub_eq_sub_iff_add_eq_add, ← mul_sub, hf, hf,
        neg_sq, neg_sq, add_sub_add_right_eq_sub, mul_assoc, mul_assoc, ← mul_sub,
        ← neg_add, ← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h3
      exact h3.resolve_left two_ne_zero
    replace h0 (x) : f x + f (-x) = -2 := by
      have h3 := h0 (-x)
      rw [neg_sq, h0, add_comm, ← sub_eq_sub_iff_add_eq_add, ← mul_sub,
        sq_sub_sq, ← neg_sub, mul_neg, ← neg_mul, ← sub_eq_zero,
        ← sub_mul, mul_eq_zero, add_comm, sub_eq_zero, sub_eq_zero] at h3
      rcases h3 with h3 | h3; exact h3.symm
      rw [not_forall] at h2; rcases h2 with ⟨t, h2⟩
      replace h0 : f t - f (-t) = f x * (f (-(x + t)) - f (x + t)) := by
        have h4 := h (-x) (x + t); rwa [neg_add_cancel_left, neg_neg, h3, ← mul_sub] at h4
      replace h : f (x + t) - f (-(x + t)) = f x * (f (-t) - f t) := by rw [h, h3, mul_sub]
      rw [← neg_sub (f (x + t)), h, ← mul_neg, neg_sub, ← mul_assoc, ← sq, ← sub_eq_zero,
        ← one_sub_mul, mul_eq_zero, or_iff_left (sub_ne_zero_of_ne (Ne.symm h2)),
        sub_eq_zero, eq_comm, sq_eq_one_iff, or_iff_right (h1 h3).ne] at h0
      rw [h3, h0, ← two_mul, mul_neg_one]
    replace h0 (x) : f (-x) = -(f x + 2) := by rw [neg_add, ← h0 x, neg_add_cancel_left]
    intro x y; specialize h x y
    rwa [h0, sub_neg_eq_add, h0, h0, neg_mul_neg, ← add_assoc, ← two_mul, add_mul,
      mul_add, mul_add, ← mul_add_one, add_assoc, add_sub_cancel_left, mul_comm (f x),
      ← mul_add, ← mul_add, ← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero,
      or_iff_right two_ne_zero, ← one_add_one_eq_two, ← add_assoc, add_add_add_comm] at h
  ---- Case 2: `f` is even
  · suffices ∀ x, f x = -1 from λ x y ↦ by rw [this, this, this, neg_add_cancel, zero_add]
    have X : (0 : S) < 2 := zero_lt_two
    replace h1 (t) : f t < 1 := h1 (h2 t)
    replace h (x) : f (x + x) = -1 := by
      have h3 := hf x (-x)
      rw [add_neg_cancel, h, neg_one_sq, neg_sq, h2, ← hf, eq_comm, sq_eq_one_iff] at h3
      exact h3.resolve_left (h1 _).ne
    replace h2 (x) : f x = -1 ∨ (0 < f x ∧ 2 * 2 * (f x ^ 2 + f x) = 1) := by
      specialize hf x x
      rw [h, h, neg_one_sq, ← two_mul, h0, mul_assoc, ← sq] at hf
      refine (le_total (2 * (f x ^ 2 + 2 * f x)) (-1)).imp (λ h3 ↦ ?_) (λ h3 ↦ ?_)
      · rw [max_eq_right h3, eq_add_neg_iff_add_eq, ← two_mul, ← sub_eq_zero, ← mul_sub,
          mul_eq_zero, or_iff_right two_ne_zero, sub_eq_zero, eq_comm, sq_eq_one_iff] at hf
        exact hf.resolve_left (h1 _).ne
      · have h4 : -1 ≤ f x := by
          rw [← neg_neg (f x), neg_le_neg_iff]
          refine le_of_not_gt λ h4 ↦ hf.not_lt
            ((add_le_add_left (le_max_right _ _) _).trans_lt' ?_)
          rw [lt_add_neg_iff_add_lt, ← two_mul, ← neg_sq, mul_lt_mul_left X, sq]
          exact one_lt_mul h4.le h4
        rw [max_eq_left h3, ← mul_add, ← add_assoc, ← two_mul, ← mul_add, ← mul_assoc] at hf
        refine ⟨lt_of_not_ge λ h5 ↦ hf.not_gt (zero_lt_one.trans_le' ?_), hf.symm⟩
        rw [sq, ← mul_add_one (f x), ← sq]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
          (mul_nonpos_of_nonpos_of_nonneg h5 (neg_le_iff_add_nonneg.mp h4))
    intro x; refine (h2 (x ^ 2)).elim (λ h3 ↦ ?_) (λ h3 ↦ (h2 x).resolve_right λ h4 ↦ ?_)
    · rwa [h0, eq_neg_iff_add_eq_zero, ← one_pow 2, ← mul_one (2 * _),
        ← add_sq, sq_eq_zero_iff, ← eq_neg_iff_add_eq_zero] at h3
    · refine (h3.2.trans h4.2.symm).not_gt (mul_lt_mul_of_pos_left ?_ (mul_pos X X))
      have h5 : f x < f (x ^ 2) := by
        rw [h0, two_mul, ← add_assoc, lt_add_iff_pos_left]
        exact add_pos (pow_pos h4.1 2) h4.1
      rw [sq, sq]; exact add_lt_add (mul_lt_mul h5 h5.le h4.1 h3.1.le) h5

/-- Final solution -/
theorem final_solution :
    good f ↔ (f = 0 ∨ ∃ φ : R →+* S, f = φ) ∨ (f = -1 ∨ ∃ φ : R →+* S, f = φ - 1) :=
  ⟨λ h ↦ (good_map_zero h).imp (good_case_one h) (good_case_two h), λ h ↦ by
    rcases h with (rfl | ⟨φ, rfl⟩) | (rfl | ⟨φ, rfl⟩)
    exacts [zero_is_good, hom_is_good φ, neg_one_is_good, hom_sub_one_is_good φ]⟩
