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

variable [LinearOrderedRing R] [FloorRing R] [LinearOrderedRing S] [FloorRing S]

namespace FloorRing

theorem DenselyOrdered_of_Ioo01 {x : R} (h : 0 < x) (h0 : x < 1) : DenselyOrdered R :=
  ⟨λ a b h1 ↦ ⟨a + x * (b - a), lt_add_of_pos_right a (mul_pos h (sub_pos_of_lt h1)),
    add_lt_of_lt_sub_left (mul_lt_of_lt_one_left (sub_pos_of_lt h1) h0)⟩⟩

def IntEquiv_of_Ioo01 (h : ¬∃ x : R, 0 < x ∧ x < 1) : ℤ ≃+* R :=
  { Int.castRingHom R with
    invFun := Int.floor
    left_inv := Int.floor_intCast
    right_inv := λ y ↦ by
      rw [eq_comm, ← sub_eq_zero]
      refine (Int.fract_nonneg y).eq_or_gt.resolve_right λ h0 ↦ ?_
      exact h ⟨_, h0, Int.fract_lt_one y⟩ }

theorem IntEquiv_apply (φ : R ≃+* ℤ) : ⇑φ = Int.floor := by
  refine (φ.eq_comp_symm id Int.floor).mp (funext λ x ↦ (?_ : x = ⌊φ.symm x⌋))
  rw [eq_intCast, Int.floor_intCast]

theorem dense_or_equiv_Int : DenselyOrdered R ∨ Nonempty (ℤ ≃+* R) :=
  (em (∃ x : R, 0 < x ∧ x < 1)).imp
    (λ ⟨_, h, h0⟩ ↦ DenselyOrdered_of_Ioo01 h h0) (λ h ↦ ⟨IntEquiv_of_Ioo01 h⟩)

end FloorRing





/-! ### `good`, `MonoidGood`, and homomorphisms -/

theorem Int_good_iff_MonoidGood {f : ℤ → R} : good f ↔ MonoidGood f :=
  forall₂_congr λ m n ↦ by rw [Int.floor_int, smul_eq_mul, id_def]

theorem good_iff_MonoidGood_equiv_Int (φ : ℤ ≃+* R) {f : R → S} : good f ↔ MonoidGood f := by
  rw [MonoidGood.ofMonoidEquiv φ.toMulEquiv, ← Int_good_iff_MonoidGood]
  refine ⟨λ hf m n ↦ Eq.trans (by simp) (hf _ _), λ hf x y ↦ ?_⟩
  specialize hf (φ.symm x) (φ.symm y); change f (φ _) = f (φ _) * ⌊f (φ _)⌋ at hf
  rw [zsmul_eq_mul, φ.map_mul, φ.apply_symm_apply, φ.apply_symm_apply] at hf
  rw [← hf, FloorRing.IntEquiv_apply, eq_intCast,
    Int.floor_int, id_eq, Int.cast_id, zsmul_eq_mul]





/-! ### Final solution -/

/-- Final solution, densely ordered version -/
alias final_solution_DenselyOrdered := good_iff_of_DenselyOrdered

/-- Final solution, `≃+* ℤ` version -/
theorem final_solution_equiv_Int (φ : ℤ ≃+* R) {f : R → S} :
    good f ↔ MonoidGood.IsAnswer f :=
  (good_iff_MonoidGood_equiv_Int φ).trans MonoidGood.solution

open scoped Classical

/-- Final solution -/
theorem final_solution [LinearOrderedRing S] [FloorRing S] {f : R → S} :
    good f ↔ if DenselyOrdered R then (∃ C, ⌊C⌋ = 1 ∧ f = λ _ ↦ C) ∨ f = 0
      else MonoidGood.IsAnswer f := by
  split_ifs with h
  · exact final_solution_DenselyOrdered
  · obtain ⟨φ⟩ : Nonempty (ℤ ≃+* R) := FloorRing.dense_or_equiv_Int.resolve_left h
    exact final_solution_equiv_Int φ
