/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5Defs
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Tactic.Ring

/-!
# IMO 2012 A5 (`x ↦ x^2 - 1`)

We show that the map `x : R ↦ x^2 - 1` on a commutative ring `R` is a good map.
For the purpose of the problem, this map's codomain is restricted
  to the subring `R_2 ⊆ R` generated by the squares in `R`.
-/

namespace IMOSL
namespace IMO2012A5

/-- The square subring of `R`, as a subgroup of `R` -/
def SqSubring (R) [CommRing R] : Subring R :=
  let R₂ := AddSubgroup.closure (Set.range λ x : R ↦ x ^ 2)
  { R₂ with
    mul_mem' :=
      have h1 : 0 ∈ R₂ := AddSubgroup.subset_closure ⟨0, zero_pow (Nat.succ_ne_zero 1)⟩
      λ h h0 ↦ AddSubgroup.closure_induction₂ h h0
        (λ _ ⟨c, h2⟩ _ ⟨d, h3⟩ ↦ h2 ▸ h3 ▸ mul_pow c d 2 ▸
          AddSubgroup.subset_closure ⟨c * d, rfl⟩)
        (λ x ↦ (zero_mul x).symm ▸ h1)
        (λ x ↦ (mul_zero x).symm ▸ h1)
        (λ x₁ x₂ y ↦ add_mul x₁ x₂ y ▸ R₂.add_mem)
        (λ x y₁ y₂ ↦ mul_add x y₁ y₂ ▸ R₂.add_mem)
        (λ x y ↦ neg_mul x y ▸ R₂.neg_mem)
        (λ x y ↦ mul_neg x y ▸ R₂.neg_mem)
    one_mem' := AddSubgroup.subset_closure ⟨1, one_pow 2⟩ }


variable [CommRing R]

def RestrictedSq (x : R) : SqSubring R :=
  ⟨x ^ 2, AddSubgroup.subset_closure ⟨x, rfl⟩⟩

theorem RestrictedSq_coe (x : R) : (RestrictedSq x : R) = x ^ 2 := rfl

theorem RestrictedSq_apply_zero : RestrictedSq (R := R) 0 = 0 :=
  Subtype.ext <| zero_pow (Nat.succ_ne_zero 1)

theorem sq_sub_one_is_good : good (λ (x : R) ↦ x ^ 2 - 1) :=
  λ _ _ ↦ by ring

theorem RestrictedSq_sub_one_is_good : good (RestrictedSq (R := R) - 1) :=
  λ x y ↦ Subtype.ext (sq_sub_one_is_good x y)

theorem RestrictedSq_sub_one_is_NontrivialGood :
    NontrivialGood (RestrictedSq (R := R) - 1) :=
  ⟨RestrictedSq_sub_one_is_good, (sub_add_cancel _ _).trans RestrictedSq_apply_zero⟩
