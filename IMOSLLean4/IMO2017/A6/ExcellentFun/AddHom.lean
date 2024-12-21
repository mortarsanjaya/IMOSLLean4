/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.ExcellentFun.Defs
import Mathlib.Algebra.Group.Hom.Instances

/-!
# Group homomorphism as excellent function

Every (additive) group homomorphism from $R$ to $G$ is an excellent function.
Thus, we have a map from $\text{Hom}(R, G)$ to the set of exellent functions.
We are mainly interested in classifying pairs $(R, G)$ such that the converse holds:
  the only excellent functions from $R$ to $G$ are group homomorphisms.

The function `ofAddMonoidHom` provides an inclusion from $\text{Hom}(R, G)$
  to the set of exellent functions from $R$ and $G$.
The typeclass `IsOfAddMonoidHomSurjective R G` indicates that this map is surjective.
When this holds, `toAddMonoidHom` gives an explicit inverse of `ofAddMonoidHom`.
-/

namespace IMOSL
namespace IMO2017A6
namespace ExcellentFun

variable [NonAssocRing R]

/-! ### Excellent functions from group homomorphisms -/

def ofAddMonoidHom [AddZeroClass G] (φ : R →+ G) : ExcellentFun R G where
  toFun := φ
  excellent_def' x y := by rw [← φ.map_add, sub_add_sub_cancel']

theorem ofAddMonoidHom_injective [AddZeroClass G] :
    (ofAddMonoidHom (R := R) (G := G)).Injective :=
  λ _ _ h ↦ AddMonoidHom.ext λ _ ↦ ExcellentFun.ext_iff.mp h _

def HomOfAddMonoidHom [AddCommMonoid G] : (R →+ G) →+ ExcellentFun R G where
  toFun := ofAddMonoidHom
  map_add' _ _ := rfl
  map_zero' := rfl

theorem HomOfAddMonoidHom_injective [AddCommMonoid G] :
    Function.Injective (HomOfAddMonoidHom (R := R) (G := G)) :=
  ofAddMonoidHom_injective





/-! ### When does excellent functions consists only of group homomorphisms? -/

class IsOfAddMonoidHomSurjective (R G) [NonAssocRing R] [AddZeroClass G] : Prop where
  ofAddMonoidHom_surjective : (ofAddMonoidHom (R := R) (G := G)).Surjective

theorem IsOfAddMonoidHomSurjective.mk' [AddZeroClass G] [IsCancelAdd G]
    (h : ∀ (f : ExcellentFun R G) (x y : R), f (x + y) = f x + f y) :
    IsOfAddMonoidHomSurjective R G where
  ofAddMonoidHom_surjective f := ⟨⟨⟨f, excellent_map_zero f⟩, h f⟩, rfl⟩


section

variable [AddZeroClass G] [IsOfAddMonoidHomSurjective R G]

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
