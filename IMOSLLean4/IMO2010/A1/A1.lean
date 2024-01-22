/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.Ring.Equiv
import Mathlib.GroupTheory.Submonoid.Basic
import Mathlib.Algebra.Function.Indicator

/-!
# IMO 2010 A1 (P1)

A *floor function* $⌊⬝⌋ : R → ℤ$ on a totally ordered ring $R$
  is a function such that, for any $r ∈ R$ and $n ∈ ℤ$,
$$ n ≤ ⌊r⌋ ↔ n ≤ r. $$

Let $R$ and $S$ be totally ordered rings with floor.
Find all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(⌊x⌋ y) = ⌊f(y)⌋ f(x). $$

### TODO

Implement the case where `R = ℤ`.
-/

namespace IMOSL
namespace IMO2010A1

/-! ### The interval (0, 1) on a floor ring -/

section FloorRing

variable [LinearOrderedRing R] [FloorRing R]

/-- An isomorphism `ℤ → R` given that `x < 1 → x ≤ 0` in `R` -/
def IntEquiv_of_zero_one_discrete (h : ∀ x : R, x < 1 → x ≤ 0) : ℤ ≃+* R :=
  { Int.castRingHom R with
    invFun := Int.floor
    left_inv := Int.floor_intCast
    right_inv := λ x ↦ (Int.floor_le x).antisymm <| le_of_sub_nonpos <|
      h _ (sub_left_lt_of_lt_add (Int.lt_floor_add_one x)) }

/-- A floor ring is either isomorphic to `ℤ` or -/
theorem exists_equiv_Int_or_zero_one_dense :
    Nonempty (ℤ ≃+* R) ∨ (∃ x : R, 0 < x ∧ x < 1) :=
  (em (∀ x : R, x < 1 → x ≤ 0)).imp
    (λ h ↦ ⟨IntEquiv_of_zero_one_discrete h⟩)
    (λ h ↦ (not_forall.mp h).elim λ x h ↦
      ⟨x, (not_imp.mp h).symm.imp_left lt_of_not_le⟩)

theorem FloorRing_zero_one_dense [h : IsEmpty (ℤ ≃+* R)] :
    ∃ x : R, 0 < x ∧ x < 1 :=
  by_contra λ h0 ↦ h.false <| IntEquiv_of_zero_one_discrete
    λ x h1 ↦ le_of_not_lt λ h2 ↦ h0 ⟨x, h2, h1⟩

end FloorRing



/-! ### Extra lemmas -/

lemma zsmul_left_eq_self₀ [Ring R] [CharZero R] [IsDomain R] {n : ℤ} {x : R} :
    n • x = x ↔ n = 1 ∨ x = 0 := by
  rw [zsmul_eq_mul, mul_left_eq_self₀, Int.cast_eq_one]





/-! ### Start of the problem -/

section general

variable [LinearOrderedRing R] [FloorRing R]
  [LinearOrderedRing S] [FloorRing S]

def good (f : R → S) := ∀ x y : R, f (⌊x⌋ • y) = ⌊f y⌋ • f x



/-! ##### General case -/

lemma good_zero : good (0 : R → S) :=
  λ _ _ ↦ (zsmul_zero _).symm

lemma good_const_of_floor_eq_one (h : ⌊(C : S)⌋ = 1) :
    good (Function.const R C) :=
  λ _ _ ↦ h ▸ (one_zsmul _).symm

variable {f : R → S} (h : good f)

lemma map_zero_eq_zero_or_const_floor_eq_one :
    f 0 = 0 ∨ ∃ C : S, ⌊C⌋ = 1 ∧ f = Function.const R C := by
  have h0 := h 0 0
  rw [zsmul_zero, eq_comm, zsmul_left_eq_self₀] at h0
  refine h0.symm.imp_right λ h0 ↦ ⟨f 0, h0, funext λ x ↦ ?_⟩
  specialize h x 0; rwa [zsmul_zero, h0, one_zsmul, eq_comm] at h

lemma floor_map_one_eq_one_or_eq_one_or_eq_zero : ⌊f 1⌋ = 1 ∨ f = 0 := by
  have h0 := h 1 1
  rw [Int.floor_one, one_zsmul, eq_comm, zsmul_left_eq_self₀] at h0
  refine h0.imp_right λ h0 ↦ funext λ x ↦ ?_
  specialize h 1 x; rwa [Int.floor_one, one_zsmul, h0, zsmul_zero] at h

lemma solution_of_zero_one_dense (hc : ∃ x : R, 0 < x ∧ x < 1) :
    f = 0 ∨ ∃ C : S, ⌊C⌋ = 1 ∧ f = Function.const R C :=
  (map_zero_eq_zero_or_const_floor_eq_one h).imp_left λ h0 ↦
    (floor_map_one_eq_one_or_eq_one_or_eq_zero h).symm.elim id λ h1 ↦ by
  rcases hc with ⟨c, hc⟩
  have h2 := h c 1
  rw [Int.floor_eq_zero_iff.mpr ⟨hc.1.le, hc.2⟩,
    h1, one_zsmul, zero_zsmul, h0] at h2
  replace h0 : ⌊(-1 : R)⌋ = -1 := by
    rw [← Int.cast_one, ← Int.cast_neg, Int.floor_intCast]
  replace h1 := h (-1) c
  rw [h0, neg_one_zsmul, ← h2, Int.floor_zero, zero_zsmul] at h1
  replace hc : ⌊-c⌋ = -1 := by
    rw [Int.floor_eq_iff, Int.cast_neg, Int.cast_one, neg_add_self]
    exact ⟨neg_le_neg hc.2.le, neg_lt_zero.mpr hc.1⟩
  replace h2 := h (-c) 1
  rw [hc, neg_one_zsmul, h1, zsmul_zero] at h2
  funext x; specialize h (-1) (-x)
  rwa [h0, neg_one_zsmul, h2, zsmul_zero, neg_neg] at h

/-- Final solution for the case where `R` is not isomorphic to `ℤ` -/
theorem final_solution_non_Int [IsEmpty (ℤ ≃+* R)] {f : R → S} :
    good f ↔ f = 0 ∨ ∃ C : S, ⌊C⌋ = 1 ∧ f = Function.const R C :=
  ⟨λ h ↦ solution_of_zero_one_dense h FloorRing_zero_one_dense,
  λ h ↦ by rcases h with rfl | ⟨C, h, rfl⟩
           exacts [good_zero, good_const_of_floor_eq_one h]⟩

end general
