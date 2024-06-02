/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2010.A1.A1Dense
import IMOSLLean4.IMO2010.A1.A1Monoid
import Mathlib.Algebra.Ring.Equiv

/-!
# IMO 2010 A1 (P1)

Let $R$ and $S$ be totally ordered rings with floor.
(See mathlib's `FloorRing`.)
Find all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(⌊x⌋ y) = f(x) ⌊f(y)⌋. $$
-/

namespace IMOSL
namespace IMO2010A1

section

variable [LinearOrderedRing R] [FloorRing R]

theorem FloorRing_dense_or_equiv_Int : DenselyOrdered R ∨ Nonempty (ℤ ≃+* R) :=
  (em (∃ x : R, 0 < x ∧ x < 1)).imp
    ---- Case 1: There exists `x : R` such that `0 < x < 1`
    (λ ⟨x, h, h0⟩ ↦ ⟨λ a b h1 ↦ ⟨a + x * (b - a),
      lt_add_of_pos_right a (mul_pos h (sub_pos_of_lt h1)),
      add_lt_of_lt_sub_left (mul_lt_of_lt_one_left (sub_pos_of_lt h1) h0)⟩⟩)
    ---- Case 2: There does not exist `x : R` such that `0 < x < 1`
    (λ h ↦ ⟨{ Int.castRingHom R with
      invFun := Int.floor
      left_inv := Int.floor_intCast
      right_inv := λ y ↦ Eq.symm <| eq_of_sub_eq_zero <| (Int.fract_nonneg y).eq_or_lt.elim
        Eq.symm λ h0 ↦ h.elim ⟨_, h0, Int.fract_lt_one y⟩ }⟩)

theorem Int_good_iff_MonoidGood {f : ℤ → R} : good f ↔ MonoidGood f :=
  forall₂_congr λ m n ↦ by rw [Int.floor_int, smul_eq_mul, id_def]

end





/-! ### Final solution -/

/-- Final solution, densely ordered version -/
alias final_solution_DenselyOrdered := good_iff_of_DenselyOrdered

open scoped Classical

/-- Final solution, `ℤ` version -/
theorem final_solution_Int [LinearOrderedRing R] [FloorRing R] {f : ℤ → R} :
    good f ↔
      (∃ φ : ℤ →* ℤ, f = λ x ↦ (φ x : R)) ∨
      (∃ (ε : R) (_ : 0 < ε) (_ : ∀ k : ℕ, k • ε < 1),
        ∃ φ : ℤ →* ℕ, f = λ x ↦ (1 + ε) * φ x) ∨
      (∃ (A : Set ℤ) (_ : ∀ m n : ℤ, m * n ∈ A ↔ m ∈ A ∧ n ∈ A) (C : R) (_ : ⌊C⌋ = 1),
        f = (if · ∈ A then C else 0)) :=
  Int_good_iff_MonoidGood.trans MonoidGood.solution
