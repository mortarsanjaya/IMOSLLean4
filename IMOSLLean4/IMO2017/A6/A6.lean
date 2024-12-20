/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6SpecificCases.TorsionFree
import IMOSLLean4.IMO2017.A6.A6SpecificCases.DivisionRing
import IMOSLLean4.IMO2017.A6.A6SpecificCases.CharTwoUnit
import IMOSLLean4.IMO2017.A6.A6RingCon
import IMOSLLean4.IMO2017.A6.ExcellentFun.RingCon
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

variable [Ring R] [AddCancelMonoid G] [ExcellentFun.IsOfAddMonoidHomSurjective R G]

/-- Classification of non-periodic good functions. -/
theorem exists_eq_NonperiodicGoodFun_iff {ι : G →+ R} [IsForallInjective ι] {f : R → G} :
    (∃ f' : NonperiodicGoodFun ι, f' = f) ↔
      ∃ (a : CentralInvolutive R) (φ : {φ : R →+ G // ∀ x, ι (φ x) = x}),
        f = λ x ↦ φ.1 (a * (1 - x)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩; let p := f.toProdCenterHom
    exact ⟨p.1, p.2, funext <| NonperiodicGoodFun.ext_iff.mp
      (toProdCenterHom_ofProdCenterHom f).symm⟩
  · rintro ⟨a, φ, rfl⟩; exact ⟨ofProdCenterHom ι ⟨a, φ⟩, rfl⟩

/-- Classification of good functions. -/
theorem exists_eq_GoodFun_iff {ι : G →+ R}
    [∀ rc : RingCon R, IsForallInjective (rc.mk'.toAddMonoidHom.comp ι)] {f : R → G} :
    (∃ f' : GoodFun ι, f' = f) ↔
      ∃ (rc : RingCon R) (a : CentralInvolutive rc.Quotient)
        (φ : {φ : rc.Quotient →+ G // ∀ x, ι (φ x) = x}),
          f = λ x ↦ φ.1 (a * (1 - rc.toQuotient x)) := by
  simp_rw [(GoodFun.AddMonoidHomNonperiodicCorrespondence ι).exists_congr_left,
    Sigma.exists, GoodFun.AddMonoidHomNonperiodicCorrespondence_symm_def]
  refine exists_congr λ rc ↦ ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩; let p := f.toProdCenterHom
    refine ⟨p.1, p.2, funext λ x ↦ ?_⟩
    rw [f.lift_def]; exact NonperiodicGoodFun.ext_iff.mp
      (toProdCenterHom_ofProdCenterHom f).symm x
  · rintro ⟨a, φ, rfl⟩; exact ⟨ofProdCenterHom _ ⟨a, φ⟩, rfl⟩

end





/-! ### The main results -/

/-- Final solution, $G$ is $2$- and $3$-torsion free. -/
theorem final_solution_TorsionFreeBy [Ring R] [AddCancelCommMonoid G]
    [IsTorsionFreeBy G 2] [IsTorsionFreeBy G 3] (ι : G →+ R) {f : R → G} :
    (∃ f' : GoodFun ι, f' = f) ↔
      ∃ (rc : RingCon R) (a : CentralInvolutive rc.Quotient)
        (φ : {φ : rc.Quotient →+ G // ∀ x, ι (φ x) = x}),
          f = λ x ↦ φ.1 (a * (1 - rc.toQuotient x)) :=
  exists_eq_GoodFun_iff

/-- Final solution, $R$ is a division ring with $\text{char}(R) ≠ 2$ and $ι = id_R$. -/
theorem final_solution_DivisionRing_char_ne_two
    [DivisionRing R] [IsTorsionFreeBy R 2] {f : R → R} :
    (∃ f' : GoodFun (AddMonoidHom.id R), f' = f) ↔
      (f = 0 ∨ f = (λ x ↦ 1 - x) ∨ f = (λ x ↦ x - 1)) := by
  rw [IsSimpleRing_exists_GoodFun_iff_zero_or_NonperiodicGoodFun]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩
    let a : CentralInvolutive R := f.Center
    have h (x) : f x = a * (1 - x) := f.Center_spec x
    clear_value a; have h0 : a = 1 ∨ a = -1 := DivisionRing_Central a
    revert h0; apply Or.imp
    all_goals rintro rfl; ext x
    · exact (h x).trans (one_mul _)
    · exact (h x).trans ((neg_one_mul _).trans (neg_sub _ _))
  · rintro (rfl | rfl)
    · exact ⟨NonperiodicGoodFun.ofProdCenterHom _ ⟨1, AddMonoidHom.id R, λ _ ↦ rfl⟩,
        funext λ x ↦ one_mul (1 - x)⟩
    · refine ⟨NonperiodicGoodFun.ofProdCenterHom _ ⟨-1, AddMonoidHom.id R, λ _ ↦ rfl⟩,
        funext λ x ↦ (neg_one_mul _).trans (neg_sub _ _)⟩

/-- Final solution, $R$ is a field of characteristic $2$ and $ι = id_R$. -/
theorem final_solution_Field [Field R] [CharTwo R] {f : R → R} :
    (∃ f' : GoodFun (AddMonoidHom.id R), f' = f) ↔ f = 0 ∨ f = (λ x ↦ 1 - x) := by
  rw [IsSimpleRing_exists_GoodFun_iff_zero_or_NonperiodicGoodFun]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩; ext x
    obtain rfl | h : x = 0 ∨ x ≠ 0 := eq_or_ne x 0
    · rw [sub_zero]; exact CharTwoDomain_incl_map_zero_eq_one (AddMonoidHom.id R) f
    · exact CharTwoDomain_units_incl_map_eq (AddMonoidHom.id R) f (Units.mk0 x h)
  · rintro rfl
    exact ⟨NonperiodicGoodFun.ofProdCenterHom _ ⟨1, AddMonoidHom.id R, λ _ ↦ rfl⟩,
      funext λ x ↦ one_mul (1 - x)⟩
