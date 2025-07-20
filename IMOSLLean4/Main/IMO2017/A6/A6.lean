/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2017.A6.A6SpecificCases.SimpleRing
import IMOSLLean4.Main.IMO2017.A6.A6SpecificCases.CharTwoUnit
import IMOSLLean4.Main.IMO2017.A6.A6NonperiodicSol
import IMOSLLean4.Main.IMO2017.A6.ExcellentFun.TorsionFree
import IMOSLLean4.Main.IMO2017.A6.CentralInvolutive.SimpleRing
import Mathlib.Algebra.Field.Basic

/-!
# IMO 2017 A6 (P2)

Let $R$ be a ring, $G$ be an abelian group, and $ι : R → G$ be a function.
Determine all functions $f : R → G$ such that, for any $x, y ∈ R$,
$$ f(ι(f(x)) ι(f(y))) + f(x + y) = f(xy). $$
-/

namespace IMOSL
namespace IMO2017A6

open NonperiodicGoodFun

/-- Final solution, $G$ is $2$- and $3$-torsion-free. -/
theorem final_solution_TorsionFreeBy [Ring R] [AddCancelCommMonoid G]
    (hG2 : ∀ x y : G, 2 • x = 2 • y → x = y) (hG3 : ∀ x y : G, 3 • x = 3 • y → x = y)
    (ι : G →+ R) (f : R → G) :
    IsGoodFun ι f ↔ ∃ (rc : RingCon R) (a : CentralInvolutive rc.Quotient)
      (φ : {φ : rc.Quotient →+ G // ∀ x, ι (φ x) = x}),
        f = λ x ↦ φ.1 (a * (1 - rc.toQuotient x)) := by
  refine IsGoodFun_iff_Nonperiodic.trans (exists_congr λ rc ↦ ⟨?_, ?_⟩)
  ---- `→` direction
  · rintro ⟨g, h, rfl⟩
    let ι' := rc.mk'.toAddMonoidHom.comp ι
    have : ExcellentFun.IsOfAddMonoidHomSurjective rc.Quotient G :=
      ExcellentFun.IsOfAddMonoidHomSurjective_of_TwoThreeTorsionFree hG2 hG3
    obtain ⟨a, φ, h0⟩ := exists_eq_ofCenterHom h.toNonperiodicGoodFun (ι := ι')
      (h.toNonperiodicGoodFun.injective_of_TwoTorsionFree hG2 (ι := ι'))
    exact ⟨a, φ, funext λ x ↦ NonperiodicGoodFun.ext_iff.mp h0 x⟩
  ---- `←` direction
  · rintro ⟨a, φ, rfl⟩
    let g' := ofCenterHom (rc.mk'.toAddMonoidHom.comp ι) a φ
    exact ⟨g', g'.IsNonperiodicGoodFun, rfl⟩

/-- Final solution, $R$ is a division ring with $\text{char}(R) ≠ 2$ and $ι = id_R$. -/
theorem final_solution_DivisionRing_char_ne_two [Ring R] [IsSimpleRing R]
    (hR2 : ∀ x y : R, 2 • x = 2 • y → x = y) {f : R → R} :
    IsGoodFun (AddMonoidHom.id R) f ↔ (f = 0 ∨ f = (λ x ↦ 1 - x) ∨ f = (λ x ↦ x - 1)) := by
  refine SimpleRing_IsGoodFun_iff_zero_or_Nonperiodic.trans (or_congr_right ⟨?_, ?_⟩)
  · rw [IsNonperiodicGoodFun.iff]; rintro ⟨g, rfl⟩
    obtain ⟨a, rfl⟩ := g.exists_eq_ofCenterId (g.injective_of_TwoTorsionFree hR2)
    apply a.eq_one_or_neg_one_of_IsSimpleRing.imp
    · rintro rfl; ext x
      rw [ofCenterId_apply, CentralInvolutive.one_val, one_mul]
    · rintro rfl; ext x
      rw [ofCenterId_apply, CentralInvolutive.neg_one_val, neg_one_mul, neg_sub]
  · rintro (rfl | rfl); exacts [IsNonperiodicGoodFun.one_sub, IsNonperiodicGoodFun.sub_one]

/-- Final solution, $R$ is a field of characteristic $2$ and $ι = id_R$. -/
theorem final_solution_Field [Field R] [Extra.CharTwo R] {f : R → R} :
    IsGoodFun (AddMonoidHom.id R) f ↔ f = 0 ∨ f = (λ x ↦ 1 - x) := by
  refine SimpleRing_IsGoodFun_iff_zero_or_Nonperiodic.trans (or_congr_right ⟨?_, ?_⟩)
  · rw [IsNonperiodicGoodFun.iff]; rintro ⟨g, rfl⟩
    ext x; obtain rfl | h : x = 0 ∨ x ≠ 0 := eq_or_ne x 0
    · rw [sub_zero]; exact CharTwoDomain_incl_map_zero_eq_one (AddMonoidHom.id R) g
    · exact CharTwoDomain_units_incl_map_eq (AddMonoidHom.id R) g (Units.mk0 x h)
  · rintro rfl; exact IsNonperiodicGoodFun.one_sub
