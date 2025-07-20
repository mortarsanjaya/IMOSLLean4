/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.A5.A5Defs

/-!
# IMO 2012 A5 (The zero map)

We show that the zero map `0 : R → S` is a good map.
Furthermore, if `f` is good and `f(0) ≠ -1`, then `f` has to be the zero map.
-/

namespace IMOSL
namespace IMO2012A5

variable [NonAssocSemiring R] [NonAssocSemiring S]

theorem zero_is_good : good (λ _ : R ↦ (0 : S)) :=
  λ _ _ ↦ by rw [add_zero, zero_mul]

theorem good_Nontrivial_or_eq_zero [IsCancelAdd S] [NoZeroDivisors S]
    {f : R → S} (h : good f) : NontrivialGood f ∨ f = (λ _ ↦ 0) :=
  ---- First get `f(1) = 0`
  have h0 : f 1 = 0 := zero_eq_mul_self.mp <| add_right_cancel (b := f (1 + 1)) <| by
    rw [zero_add, ← h, one_mul]
  ---- Next get `f(x) (f(0) + 1) = 0` for all `x : R`
  have h1 (x : R) : 0 = f x * (f 0 + 1) := by
    have h1 := h x 0; rwa [mul_zero, zero_add, h0, add_zero, ← mul_add_one (f x)] at h1
  ---- Elimination
  (zero_eq_mul.mp (h1 0)).symm.imp (λ h1 ↦ ⟨h, h1⟩)
    (λ h2 ↦ funext λ x ↦ by specialize h1 x; rwa [h2, zero_add, mul_one, eq_comm] at h1)

theorem good_iff_Nontrivial_or_eq_zero [IsCancelAdd S] [NoZeroDivisors S] {f : R → S} :
    good f ↔ NontrivialGood f ∨ f = (λ _ ↦ 0) :=
  ⟨good_Nontrivial_or_eq_zero, λ h ↦ h.elim NontrivialGood.is_good λ h ↦ h ▸ zero_is_good⟩
