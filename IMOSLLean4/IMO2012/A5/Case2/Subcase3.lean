/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.Case2.Subcase1

/-!
# IMO 2012 A5, Subcase 2.3: $f(-1) = 0$ and $f(2) = 3 ≠ 1$

This file solves Subcase 2.3, using a lemma from Subcase 2.1.
-/

namespace IMOSL
namespace IMO2012A5

section Step9Domain

variable [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = 3)

/-- (9.1) -/
theorem case2_3_lem1 (x : R) : f (x + 2) = 3 * (f (x + 1) - f x) + f (x - 1) :=
  h1 ▸ case2_map_add_two_eq h h0 x

/-- (9.2) -/
theorem case2_3_lem2 (x : R) :
    f x * (3 * f (x - 1) + f (x + 1))
      = (f (x - 1) + 3 * f (x + 1)) * (1 + f (x - 1)) := by
  have h2 := case2_special_identity h h0 x
  rw [← h1, mul_add, eq_add_of_sub_eq h2, case2_map_add_two_eq h h0]
  ring

/-- (9.3) -/
theorem case2_3_lem3 (x : R) :
    f (x + 1) + f (x - 1) = 2 * f x + 2 ∨ f (x - 1) = f (x + 1) := by
  have X := case2_map_even h h0
  have X0 := case2_3_lem2 h h0 h1
  have h2 := X0 (-x)
  rw [X, ← neg_add', X, neg_add_eq_sub, ← neg_sub x, X] at h2
  rw [← sub_eq_zero, or_comm, ← mul_eq_mul_right_iff, ← sub_eq_zero,
    ← sub_eq_zero.mpr (congr_arg₂ (· - ·) h2 (X0 x))]
  ring

/-- (9.4) -/
theorem case2_3_lem4 (h2 : f 2 ≠ 1) (x : R) :
    f (x + 1) + f (x - 1) = 2 * f x + 2 ∨ f (x + 1) = 0 ∧ f (x - 1) = 0 := by
  -- Reduce to `f(x - 1) = 0` assuming `f(x - 1) = f(x + 1)`
  have X := case2_3_lem3 h h0 h1
  refine (X x).imp_right λ h3 ↦ ?_
  rw [← h3, and_self]
  -- Get either `f (x - 1) = 0`, `(4 : S) = 0`, or `f(x) = f(x - 1) + 1`
  have h4 := case2_3_lem2 h h0 h1 x
  rw [← h3, add_comm, ← one_add_mul (3 : S), mul_comm,
    mul_eq_mul_left_iff, mul_eq_zero, or_comm] at h4
  -- Eliminate the other two cases
  have h5 : (2 : S) ≠ 0 := λ h5 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, h5, zero_add]
  refine (h4.resolve_right ?_).resolve_left ?_
  -- Obtain contradiction via `f(x + 2) + f(x) = 2 f(x + 1) + 2`
  · intros h4; apply h5
    specialize X (x + 1)
    rwa [add_sub_cancel_right, add_assoc, one_add_one_eq_two, case2_3_lem1 h h0 h1,
      ← h3, h4, sub_add_cancel_right, mul_neg_one, add_left_inj, add_add_add_comm,
      ← two_mul, add_comm, add_right_inj, ← two_add_one_eq_three, neg_add',
      sub_add_cancel, eq_comm, eq_sub_iff_add_eq, one_add_one_eq_two, or_self,
      eq_neg_iff_add_eq_zero, ← two_mul, ← sq, sq_eq_zero_iff] at X
  · rw [← two_add_one_eq_three, add_left_comm, one_add_one_eq_two, ← two_mul]
    exact mul_ne_zero h5 h5

/-- (9.5) -/
theorem case2_3_lem5 (h2 : f 2 ≠ 1) (x : R) :
    f (x + 1) + f (x - 1) = 2 * f x + 2 ∨
      f x = 0 ∧ f (x + 1) = 0 ∧ f (x - 1) = 0 := by
  have X := case2_3_lem4 h h0 h1 h2
  refine (X x).elim Or.inl λ h3 ↦ (X (x + 1)).imp
    (λ h4 ↦ ?_) (λ h4 => ⟨add_sub_cancel_right x 1 ▸ h4.2, h3⟩)
  rw [h3.1, mul_zero, zero_add, add_assoc, one_add_one_eq_two,
    add_sub_cancel_right, case2_3_lem1 h h0 h1, h3.1, zero_sub, h3.2,
    add_zero, mul_neg, neg_add_eq_iff_eq_add, ← two_add_one_eq_three,
    add_one_mul (2 : S), add_right_comm, self_eq_add_left] at h4
  rw [h3.1, h3.2, h4, zero_add]

/-- (9.6) -/
theorem case2_3_lem6 (h2 : f 2 ≠ 1) (h3 : f 0 = -1) (x : R) :
    f (x + 1) + f (x - 1) = 2 * f x + 2 := by
  refine (case2_3_lem5 h h0 h1 h2 x).resolve_right λ h4 ↦ ?_
  by_cases h5 : f 2 = 0
  -- Case 1: `char(S) = 3`
  · have h6 : f (x - 1) + f x + f (x + 1) = -1 :=
      case2_1_lem6 (periodLift_is_good h) h0 h5
        (zero_of_periodic_periodLift h) h3 x
    rw [h4.1, h4.2.1, h4.2.2, add_zero, add_zero, zero_eq_neg] at h6
    exact one_ne_zero h6
  -- Case 2: `char(S) ≠ 3`
  · suffices (f (2 * x) = -1 ∨ f (2 * x) = 0) ∧ f (2 * x) = -3 by
      rcases this with ⟨h6 | h6, h7⟩
      · rw [h7, neg_inj, ← h1] at h6; exact h2 h6
      · rw [h7, neg_eq_zero, ← h1] at h6; exact h5 h6
    constructor
    -- `f(2x) ∈ {-1, 0}`
    · refine (case2_3_lem5 h h0 h1 h2 (2 * x)).imp (λ h6 ↦ ?_) And.left
      have h7 := h (1 + 1) (x - 1)
      rw [h4.2.2, mul_zero, add_add_sub_cancel, add_comm 1 x, h4.2.1, sub_zero,
        mul_sub_one, ← sub_sub, sub_add_cancel, one_add_one_eq_two] at h7
      have h8 := case2_good_alt h h0 (x + 1) (1 + 1)
      rw [h4.2.1, zero_mul, add_sub_add_right_eq_sub,
        h4.2.2, sub_zero, add_one_mul x, ← add_assoc,
        add_sub_cancel_right, one_add_one_eq_two, mul_comm] at h8
      rw [h7, h8, zero_add, ← mul_add_one (2 : S), zero_eq_mul] at h6
      rcases h6 with h6 | h6
      · refine absurd ?_ h2
        rw [h1, ← two_add_one_eq_three, h6, zero_add]
      · rw [eq_neg_iff_add_eq_zero, h6]
    -- `f(2x) = -3`
    · have h6 := case2_3_lem1 h h0 h1 ((x + 1) * (x - 1))
      rw [eq_add_of_sub_eq (h _ _), eq_add_of_sub_eq (case2_good_alt h h0 _ _),
        h4.2.1, zero_mul, zero_add, zero_add, ← one_add_one_eq_two, ← sq_sub_sq,
        one_pow, add_add_sub_cancel, add_sub_sub_cancel, sub_add_add_cancel,
        case2_map_sq_sub_one h h0 h3, sq, eq_add_of_sub_eq (h _ _), h4.1, sq 0,
        zero_mul, zero_add, zero_sub, ← two_mul, one_add_one_eq_two, h1,
        sub_neg_eq_add, mul_add_one (3 : S), add_assoc, ← two_mul] at h6
      nth_rw 1 [← two_add_one_eq_three] at h6
      rw [add_one_mul (α := S), add_right_comm, self_eq_add_left,
        ← mul_add, mul_eq_zero, add_eq_zero_iff_eq_neg] at h6
      apply h6.resolve_left
      rwa [h1, ← two_add_one_eq_three, add_left_ne_self] at h2

end Step9Domain



section Step9Field

variable [CommRing R] [Field S]

def homGuess (f : R → S) (x : R) := (f x - f (x - 1) + 1) / 2

variable {f : R → S} (h : good f) (h0 : f (-1) = 0)
  (h1 : f 2 = 3) (h2 : f 2 ≠ 1) (h3 : f 0 = -1)

/-- (9.g1) -/
theorem case2_3_lem_g1 : homGuess f 0 = 0 :=
  div_eq_zero_iff.mpr <| Or.inl <|
    by rw [h3, zero_sub, h0, sub_zero, neg_add_self]

/-- (9.g2) -/
theorem case2_3_lem_g2 (x : R) : homGuess f (x + 1) = homGuess f x + 1 := by
  have h4 : (2 : S) ≠ 0 := λ h4 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, h4, zero_add]
  rw [homGuess, homGuess, div_add_one h4, add_sub_cancel_right]
  refine congr_arg₂ _ ?_ rfl
  rw [add_right_comm, add_left_inj, ← add_sub_right_comm,
    eq_sub_iff_add_eq, ← add_sub_right_comm, sub_eq_iff_eq_add,
    case2_3_lem6 h h0 h1 h2 h3, two_mul, add_right_comm]

/-- Variant of (9.g2) -/
theorem case2_3_lem_g2' (x : R) : homGuess f (x - 1) = homGuess f x - 1 := by
  rw [eq_sub_iff_add_eq, ← case2_3_lem_g2 h h0 h1 h2 h3, sub_add_cancel]

/-- (9.g3) -/
theorem case2_3_lem_g3 (x : R) : homGuess f (-x) = -homGuess f x := by
  have X := case2_map_even h h0
  rw [← add_left_inj 1, ← case2_3_lem_g2 h h0 h1 h2 h3, homGuess, add_sub_cancel_right,
    X, neg_add_eq_sub, ← X, neg_sub, homGuess, ← neg_div, neg_add', neg_sub]
  replace X : (2 : S) ≠ 0 := λ h4 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, h4, zero_add]
  rw [div_add_one X, ← one_add_one_eq_two, sub_add_add_cancel]

/-- (9.g4) -/
theorem case2_3_lem_g4 (x : R) : f x = homGuess f x ^ 2 - 1 := by
  have h4 : (2 : S) ≠ 0 := λ h4 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, h4, zero_add]
  have h5 : (2 : S) ^ 2 ≠ 0 := pow_ne_zero 2 h4
  rw [homGuess, div_pow, div_sub_one h5, eq_div_iff h5]
  refine mul_left_cancel₀ h4 (eq_of_sub_eq_zero ?_).symm
  rw [← sub_eq_zero_of_eq (case2_3_lem2 h h0 h1 x),
    eq_sub_of_add_eq (case2_3_lem6 h h0 h1 h2 h3 x)]
  ring

/-- (9.g5) -/
theorem case2_3_lem_g5 (x y : R) :
    (homGuess f (x * y) + 1) ^ 2 - homGuess f (x + y) ^ 2 =
      (homGuess f x ^ 2 - 1) * (homGuess f y ^ 2 - 1) := by
  have h4 := case2_3_lem_g4 h h0 h1 h2 h3
  have h5 := h x y
  iterate 4 rw [h4] at h5
  rwa [sub_sub_sub_cancel_right, case2_3_lem_g2 h h0 h1 h2 h3] at h5

/-- (9.g6) -/
theorem case2_3_lem_g6 (x y : R) :
    (homGuess f (x * y) - 1) ^ 2 - homGuess f (x - y) ^ 2 =
      (homGuess f x ^ 2 - 1) * (homGuess f y ^ 2 - 1) := by
  have h4 := case2_3_lem_g4 h h0 h1 h2 h3
  have h5 := case2_good_alt h h0 x y
  iterate 4 rw [h4] at h5
  rwa [sub_sub_sub_cancel_right, case2_3_lem_g2' h h0 h1 h2 h3] at h5

/-- (9.g7) -/
theorem case2_3_lem_g7 (x y : R) :
    2 ^ 2 * homGuess f (x * y)
      = homGuess f (x + y) ^ 2 - homGuess f (x - y) ^ 2 := by
  rw [← sub_sub_sub_cancel_left, case2_3_lem_g5 h h0 h1 h2 h3, add_sq',
    ← case2_3_lem_g6 h h0 h1 h2 h3, sub_sub_sub_cancel_right, sub_sq',
    add_sub_sub_cancel, mul_one, ← two_mul, ← mul_assoc, ← sq]

/-- (9.g8) -/
theorem case2_3_lem_g8 (x y : R) :
    (homGuess f (x + y) ^ 2 - homGuess f (x - y) ^ 2) ^ 2 + 2 ^ 4 =
      2 ^ 3 * (homGuess f (x + y) ^ 2 + homGuess f (x - y) ^ 2) +
        (2 ^ 2) ^ 2 * ((homGuess f x ^ 2 - 1) * (homGuess f y ^ 2 - 1)) := by
  rw [← case2_3_lem_g5 h h0 h1 h2 h3, mul_sub, ← mul_pow,
    mul_add_one (α := S), case2_3_lem_g7 h h0 h1 h2 h3]
  ring

/-- TODO: Optimize the proof -/
theorem case2_3_lem_g9 (x y : R) :
    homGuess f (x + y) + homGuess f (x - y) = 2 * homGuess f x ∨
      homGuess f (x + y) + homGuess f (x - y) = -(2 * homGuess f x) := by
  have h4 : (2 : S) ≠ 0 := λ h4 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, h4, zero_add]
  rw [← sq_eq_sq_iff_eq_or_eq_neg]
  apply mul_left_cancel₀ (pow_ne_zero 3 h4)

  replace h4 := case2_3_lem_g2 h h0 h1 h2 h3
  have h5 := case2_3_lem_g2' h h0 h1 h2 h3
  have h6 := case2_3_lem_g8 h h0 h1 h2 h3 x
  replace h6 : (_ + _) - (2 * _) = _ - _ :=
    congr_arg₂ (· - ·)
      (congr_arg₂ (· + ·) (h6 (y + 1)) (h6 (y - 1)))
      (congr_arg (2 * ·) (h6 y))
  rw [← add_assoc x, h4, ← sub_sub x, h5, ← add_sub_assoc x,
    h5, ← sub_add x, h4, h4, h5] at h6
  rw [← sub_eq_zero, ← sub_eq_zero_of_eq h6]
  ring

/-- (9.g9) -/
theorem case2_3_lem_g10 (x y : R) :
    homGuess f (x + y) + homGuess f (x - y) = 2 * homGuess f x := by
  have h4 x := case2_3_lem_g9 h h0 h1 h2 h3 x y
  refine (h4 x).elim id λ h5 ↦ ?_
  have h6 := case2_3_lem_g2 h h0 h1 h2 h3
  specialize h4 (x + 1)
  rw [add_right_comm, h6, add_sub_right_comm, h6, add_add_add_comm,
    h6, mul_add_one (2 : S), one_add_one_eq_two, add_left_inj] at h4
  refine h4.resolve_right λ h4 ↦ ?_
  rw [h5, neg_add, add_right_inj, eq_neg_iff_add_eq_zero, ← two_mul,
    mul_self_eq_zero, ← add_left_eq_self, two_add_one_eq_three] at h4
  exact h2 (h1.trans h4)

theorem case2_3_sol : ∃ φ : R →+* S, f = λ x => φ x ^ 2 - 1 := by
  have X := case2_3_lem_g2 h h0 h1 h2 h3
  have X0 := case2_3_lem_g10 h h0 h1 h2 h3
  have X1 : (2 : S) ≠ 0 := λ X1 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, X1, zero_add]
  -- Zero map
  have hZero := case2_3_lem_g1 h0 h3
  -- One map
  have hOne : homGuess f 1 = 1 := by
    rw [← zero_add (1 : R), X, hZero, zero_add]
  -- Multiplicativity
  have hMul x y : homGuess f (x * y) = homGuess f x * homGuess f y := by
    have h4 := case2_3_lem_g7 h h0 h1 h2 h3 x y
    rw [sq_sub_sq, X0, sub_eq_add_neg, ← case2_3_lem_g3 h h0 h1 h2 h3,
      neg_sub, add_comm x, X0, mul_mul_mul_comm, ← sq] at h4
    exact mul_left_cancel₀ (pow_ne_zero 2 X1) h4
  -- Additivity
  have hAdd x y : homGuess f (x + y) = homGuess f x + homGuess f y := by
    specialize X0 (x + y) (x - y)
    rw [add_add_sub_cancel, add_sub_sub_cancel, ← two_mul, hMul, ← two_mul,
      hMul, ← mul_add, ← one_add_one_eq_two, X, hOne, one_add_one_eq_two] at X0
    exact (mul_left_cancel₀ X1 X0).symm
  -- Finish
  exact ⟨⟨⟨⟨homGuess f, hOne⟩, hMul⟩, hZero, hAdd⟩,
    funext <| case2_3_lem_g4 h h0 h1 h2 h3⟩

/-- Solution for the current subcase (`x ↦ φ(x)^2 - 1`) -/
theorem case2_3_IsAnswer : IsAnswer f :=
  Exists.elim (case2_3_sol h h0 h1 h2 h3)
    (λ φ h4 ↦ h4.symm ▸ IsAnswer.hom_sq_sub_one φ)

end Step9Field
