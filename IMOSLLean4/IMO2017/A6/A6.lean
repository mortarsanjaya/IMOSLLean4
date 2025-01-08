/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6SpecificCases.DivisionRing
import IMOSLLean4.IMO2017.A6.A6SpecificCases.CharTwoUnit
import IMOSLLean4.IMO2017.A6.A6NonperiodicSol
import IMOSLLean4.IMO2017.A6.ExcellentFun.TorsionFree
import IMOSLLean4.IMO2017.A6.CentralInvolutive.SimpleRing
import Mathlib.Algebra.Field.Basic

/-!
# IMO 2017 A6 (P2)

Let $R$ be a ring, $G$ be an abelian group, and $ι : R → G$ be a function.
Determine all functions $f : R → G$ such that, for any $x, y ∈ R$,
$$ f(ι(f(x)) ι(f(y))) + f(x + y) = f(xy). $$
-/

namespace IMOSL
namespace IMO2017A6

open Extra NonperiodicGoodFun

section

variable [Ring R] [AddCancelCommMonoid G] (hG2 : ∀ x y : G, 2 • x = 2 • y → x = y)
  (hG3 : ∀ x y : G, 3 • x = 3 • y → x = y) (ι : G →+ R)
include hG2 hG3 ι

/-- Final solution, $G$ is $2$- and $3$-torsion free, bundled version. -/
theorem final_solution_GoodFun_TorsionFreeBy (f : GoodFun ι) :
    ∃ (rc : RingCon R) (a : CentralInvolutive rc.Quotient)
      (φ : {φ : rc.Quotient →+ G // ∀ x, ι (φ x) = x}),
    f = (ofCenterHom (rc.mk'.toAddMonoidHom.comp ι) a φ).Lift := by
  simp_rw [← GoodFun.AddMonoidHomNonperiodicCorrespondence_symm_def, Equiv.eq_symm_apply]
  let rc := f.inducedRingCon
  let ι' := rc.mk'.toAddMonoidHom.comp ι
  have : ExcellentFun.IsOfAddMonoidHomSurjective rc.Quotient G :=
    ExcellentFun.IsOfAddMonoidHomSurjective_of_TwoThreeTorsionFree hG2 hG3
  obtain ⟨a, φ, h0⟩ := exists_eq_ofCenterHom f.Quotient (ι := ι')
    (f.Quotient.injective_of_TwoTorsionFree hG2 (ι := ι'))
  exact ⟨rc, a, φ, Eq.symm (congrArg (Sigma.mk _) h0.symm)⟩

/-- Final solution, $G$ is $2$- and $3$-torsion free. -/
theorem final_solution_TorsionFreeBy (f : R → G) :
    (∃ f' : GoodFun ι, f' = f) ↔
      ∃ (rc : RingCon R) (a : CentralInvolutive rc.Quotient)
        (φ : {φ : rc.Quotient →+ G // ∀ x, ι (φ x) = x}),
          f = λ x ↦ φ.1 (a * (1 - rc.toQuotient x)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨rc, a, φ, rfl⟩ := final_solution_GoodFun_TorsionFreeBy hG2 hG3 ι f
    exact ⟨rc, a, φ, rfl⟩
  · rintro ⟨rc, a, φ, rfl⟩
    exact ⟨(ofCenterHom (rc.mk'.toAddMonoidHom.comp ι) a φ).Lift, rfl⟩

end


/-- Final solution, $R$ is a division ring with $\text{char}(R) ≠ 2$ and $ι = id_R$. -/
theorem final_solution_DivisionRing_char_ne_two [Ring R] [IsSimpleRing R]
    (hR2 : ∀ x y : R, 2 • x = 2 • y → x = y) {f : R → R} :
    (∃ f' : GoodFun (AddMonoidHom.id R), f' = f) ↔
      (f = 0 ∨ f = (λ x ↦ 1 - x) ∨ f = (λ x ↦ x - 1)) := by
  rw [IsSimpleRing_exists_GoodFun_iff_zero_or_NonperiodicGoodFun]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨a, rfl⟩ := f.exists_eq_ofCenterId (f.injective_of_TwoTorsionFree hR2)
    apply a.eq_one_or_neg_one_of_IsSimpleRing.imp
    all_goals rintro rfl; ext x
    · rw [ofCenterId_apply, CentralInvolutive.one_val, one_mul]
    · rw [ofCenterId_apply, CentralInvolutive.neg_one_val, neg_one_mul, neg_sub]
  · rintro (rfl | rfl)
    · exact ⟨ofCenterId 1, funext λ x ↦ one_mul (1 - x)⟩
    · exact ⟨ofCenterId (-1), funext λ x ↦ (neg_one_mul _).trans (neg_sub 1 x)⟩

/-- Final solution, $R$ is a field of characteristic $2$ and $ι = id_R$. -/
theorem final_solution_Field [Field R] [CharTwo R] {f : R → R} :
    (∃ f' : GoodFun (AddMonoidHom.id R), f' = f) ↔ f = 0 ∨ f = (λ x ↦ 1 - x) := by
  rw [IsSimpleRing_exists_GoodFun_iff_zero_or_NonperiodicGoodFun]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩; ext x
    obtain rfl | h : x = 0 ∨ x ≠ 0 := eq_or_ne x 0
    · rw [sub_zero]; exact CharTwoDomain_incl_map_zero_eq_one (AddMonoidHom.id R) f
    · exact CharTwoDomain_units_incl_map_eq (AddMonoidHom.id R) f (Units.mk0 x h)
  · rintro rfl; exact ⟨ofCenterId 1, funext λ x ↦ one_mul (1 - x)⟩
