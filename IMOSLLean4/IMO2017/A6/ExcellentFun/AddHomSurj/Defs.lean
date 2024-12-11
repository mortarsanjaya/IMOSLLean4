/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.ExcellentFun.AddHom

/-!
# When does excellent functions consists only of group homomorphisms?

This file provides a typeclass `IsOfAddMonoidHomSurjective`, which states that
  for a given ring $R$ and abelian group $G$, the only excellent functions
  from $R$ to $G$ are group homomorphisms.
-/

namespace IMOSL
namespace IMO2017A6
namespace ExcellentFun

class IsOfAddMonoidHomSurjective (R G) [NonAssocRing R] [AddZeroClass G] : Prop where
  ofAddMonoidHom_surjective : (ofAddMonoidHom (R := R) (G := G)).Surjective


variable [NonAssocRing R] [AddZeroClass G]

theorem IsOfAddMonoidHomSurjective.mk' [IsCancelAdd G]
    (h : ∀ (f : ExcellentFun R G) (x y : R), f (x + y) = f x + f y) :
    IsOfAddMonoidHomSurjective R G where
  ofAddMonoidHom_surjective f := ⟨⟨⟨f, excellent_map_zero f⟩, h f⟩, rfl⟩


section

variable [IsOfAddMonoidHomSurjective R G]

theorem ofAddMonoidHom_surjective : (ofAddMonoidHom (R := R) (G := G)).Surjective :=
  IsOfAddMonoidHomSurjective.ofAddMonoidHom_surjective

/-- Choice-independent inverse of `ofAddMonoidHom` -/
def toAddMonoidHom (f : ExcellentFun R G) : R →+ G where
  toFun := f.toFun
  map_zero' := by obtain ⟨φ, rfl⟩ := ofAddMonoidHom_surjective f; exact φ.map_zero
  map_add' := by obtain ⟨φ, rfl⟩ := ofAddMonoidHom_surjective f; exact φ.map_add

theorem toAddMonoidHom_ofAddMonoidHom (φ : R →+ G) :
    toAddMonoidHom (ofAddMonoidHom φ) = φ := rfl

theorem ofAddMonoidHom_toAddMonoidHom (f : ExcellentFun R G) :
    ofAddMonoidHom (toAddMonoidHom f) = f := rfl

end
